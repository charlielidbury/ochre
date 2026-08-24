import Dllbc.Program
import Dllbc.Std
import Dllbc.StdChain
import Dllbc.ProgMacro
import Dllbc.Tests.Functions
import Dllbc.Tests.Boundaries
import Dllbc.FnMacro
import Dllbc.Tests.Arrays
import Dllbc.Tests.Direct
import Dllbc.Tests.Diff
import Dllbc.Tests.ArraySort

/-!
# Programs — binder modes, mixed-return containment, fuel-threading, and programs as terms

This file tests the split between comptime and runtime binders: a capital binder
is comptime — erased, and usable only in types and proofs — while a lowercase
binder is runtime. The tests cover the comptime-argument rule, capital `let`,
fuel-threading, erased data, borrow-typed binders being runtime-only, and the
containment that stops a borrow from leaking into the comptime fragment. Later
sections test that a program is itself just a term (a let-chain with no declared
functions) and that a recursion's result is a fully evaluated value. The closing
batteries cover the rest of the mode discipline: a function value must arrive at
a comptime destination, `Σ0` (the comptime-tail pair), comptime domains staying
transparent to the type walks, and the mode convention reaching match-arm
binders.

Why the modes matter: the split lets one language serve as both program and proof
without the proof layer ever touching runtime state.

The lemma material cited below comes from `Dllbc.StdChainRaw`, the raw proof
terms at their post-migration home (docs/20). No program here seeds from the
chain's state: every citation sits in the comptime fragment — a capital `let`'s
right-hand side, a splice at a capital argument, a λ body, a sealed proof
binding — which is the very discipline under test, and a chain call's result is
not comptime (§C3 pins exactly that). So the citations stay raw splices,
retargeted to the constants' new home; the terms are value-identical, and every
verdict and needle below is the pre-migration one unchanged.
-/

section
/-!
# Binder modes: capital is comptime, and the fence

One convention: **a capitalized binder is comptime, a lowercase one is runtime**.
It is carried by two mechanisms:

  * **The comptime-argument rule.** At a call, an argument in a capital-bindered
    position is evaluated under ⇝: a pure, non-consuming read. The binder is
    erased — never moved, citable after any call.
  * **The fence.** A capital binder is usable only in ⇝-positions (types, proofs,
    capital arguments of other calls). A move of it, a runtime match on it, a
    borrow of it, a write through it, an index of it, and a call of it are each
    rejected.

**Where the mode lives.** A *runtime* binder is a `Var` — an id and a name — so
its mode is its name's case (`Var.isComptime`); this covers telescope parameters,
`let`, and match binders. A *pure* binder's mode rides on the domain instead:
`Π (X : τ) → …` is `.pi (.cmpT τ) …`, where `Term.cmpT` marks the comptime case.

**Case is inert under conversion, mechanically.** Conversion unwraps `cmpT` on
either side, so it cannot observe a mode: the two Π's in §E convert, and the same
two Π's give different call behaviour. Modes route a call's arguments and fence
its body; conversion is the place the distinction was never meant to reach.

**Negative controls are per demand site.** A rule branch nobody demands is a rule
branch nobody tested, so each rejection below is paired with the lowercase twin
that is accepted — which shows the rejection is about the mode and not about the
program.
-/

open Dllbc
open Dllbc.StdChainRaw (LeReflRaw LeTransRaw)
open Dllbc.Tests.S9Diff (diffC)

namespace Dllbc.Tests.S26Modes

/-! ## §A. The comptime-argument rule

    Passing a proof to a call ordinarily moves it, which forces callers needing
    it afterwards to stage it into a closure before the call. A capital
    parameter avoids that: the argument is read under ⇝ instead of moved.

    The subject must be a telescope proof, not a `let`-bound one: a proof spine
    is already index-kind and copies on read, so it would show nothing. A
    telescope proof's type is a stuck recursor spine, which is the class this
    rule is about. -/

-- `useLe` and its capital twin `useLeC` are the callees of every pair below, one
-- character apart, each written as one chain (callee above caller).

-- A1. The proof is passed, and citing it afterwards is a use-after-move.
def a1 : Term := prog_parse {
  fn UseLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { UseLe(n, m, hnm); hnm };
  () }
example : progRejects a1 "holds ⊥" = true := by native_decide

-- A2. The same program against the capital twin: accepted, because the argument
-- was ⇝-read and never left the caller's slot.
def a2 : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { UseLeC(n, m, hnm); hnm };
  () }
example : progOk a2 = true := by native_decide

-- A3. …and it is not a one-shot: passed twice, cited after both.
def a3 : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { UseLeC(n, m, hnm); UseLeC(n, m, hnm); hnm };
  () }
example : progOk a3 = true := by native_decide

-- A4. The old staging trick — capture a proof into a closure before the call
-- that consumes it — still works, and is now unnecessary: A3 is the same
-- program without it.
def a4 : Term := prog{
  fn UseLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let Hnm = hnm;                          -- named so the closure can cite it
    let Mk = λ (u : Unit). Hnm; UseLe(n, m, hnm); Mk unit };
  () }
example : progOk a4 = true := by native_decide

/-! ### A5. `match fuel` against its capital twin

    A lowercase binder is branched on; the capital twin — same type, same
    position — cannot be. This is the pair that shows the modes are doing work
    rather than decorating. -/

def a5lo : Term := prog{ fn A5lo (fuel : Nat) -> Unit { match fuel { Z => (), S(f2) => () } }; () }
def a5hi : Term := prog_parse { fn A5hi (Fuel : Nat) -> Unit { match Fuel { Z => (), S(f2) => () } }; () }
example : progOk a5lo = true := by native_decide
example : progRejects a5hi "cannot be the scrutinee of a runtime match" = true := by native_decide

-- A6. A comptime argument must be a comptime term. A call's result is a fresh
-- existential with no ⇝ reading, so it cannot be spliced into a capital position
-- directly — it must be `let`-bound first. An honest rejection rather than a
-- silent fall-back to a move; the `let`-bound form below works.
def a6bad : Term := prog_parse {
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn GiveLe (a : Nat) -> Le a a { LeReflRaw a };
  fn Caller (n : Nat) -> Unit { UseLeC(n, n, GiveLe(n)); () };
  () }
def a6ok : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn GiveLe (a : Nat) -> Le a a { LeReflRaw a };
  fn Caller (n : Nat) -> Unit
  { let p = GiveLe(n); UseLeC(n, n, p); UseLeC(n, n, p); () };
  () }
example : progRejects a6bad "not in the comptime fragment" = true := by
  native_decide
example : progOk a6ok = true := by native_decide

/-! ## §B. The fence — one control per demand site, each with its lowercase twin

    A rule branch nobody demands is a rule branch nobody tested. The sites below
    are the rules that would make an erased binder observable, each paired with
    the same program over a lowercase binder, which is accepted. That pairing is
    the liveness check: it shows the rejection is about the mode, not about the
    program being ill-formed some other way. -/

-- B1. The ⇒-move.
def b1hi : Term := prog_parse { fn B1 (N : Nat) -> Unit { let y = N; () }; () }
def b1lo : Term := prog{ fn B1 (n : Nat) -> Unit { let y = n; () }; () }
example : progRejects b1hi "cannot be ⇒-moved" = true := by native_decide
example : progOk b1lo = true := by native_decide

-- B2. The runtime match — §A5 above, which is where it earns its keep.

-- B3. The borrow.
def b3hi : Term := prog_parse { fn B3 (N : List Nat) -> Unit { let b = &m N; () }; () }
def b3lo : Term := prog{ fn B3 (n : List Nat) -> Unit { let b = &m n; () }; () }
example : progRejects b3hi "cannot be borrowed" = true := by native_decide
example : progOk b3lo = true := by native_decide

-- B4. The write-through (⇐).
def b4hi : Term := prog_parse { fn B4 (N : Nat) -> Unit { N := 3; () }; () }
def b4lo : Term := prog{ fn B4 (n : Nat) -> Unit { n := 3; () }; () }
example : progRejects b4hi "cannot be written through" = true := by native_decide
example : progOk b4lo = true := by native_decide

-- B5. The index/slice step. The fence fires on the place's syntactic root
-- before the place is navigated at all, which is the property being pinned (a
-- place expression may carve, and a fence that ran after that would have
-- already reorganized the state). `N[Z]` is the `a[i]` row — `.index N Z none`
-- — and the surface elaborates it on a comptime binder without complaint; the
-- refusal is the checker's.
def b5hi : Term := prog_parse { fn B5 (N : Nat) -> Unit { let e = N[Z]; () }; () }
example : progRejects b5hi "cannot be indexed or sliced" = true := by native_decide

-- B6. A capital binder handed to a lowercase parameter. Same rejection as B1,
-- at a different demand site: passing an erased binder to a runtime parameter
-- moves it there. This is the direction that makes the fence coherent — a
-- comptime binder cannot launder itself into runtime by being passed to
-- something that wants a runtime value.
def b6 : Term := prog_parse {
  fn UseLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, Hnm : Le n m) -> Unit
  { UseLe(n, m, Hnm); () };
  () }
example : progRejects b6 "cannot be ⇒-moved" = true := by native_decide

/-! ### B7. A function-typed parameter is both citable and callable in either case

    A call's head is fetched by ⇝, which is how a capital binder is read anyway,
    so a capital function-typed parameter can be cited in a type AND called —
    there is no separate "spec parameter" kind that only does one of the two.
    The two tests below check the same case through each of the parameter's two
    uses. -/

def b7spec : Term := prog{
  fn B7spec (G : Π (x : Nat) → Nat, n : Nat) -> Unit { let r = G(n); () };
  () }
example : progOk b7spec = true := by native_decide
example : progOk S26Seal.apply1 = true := by native_decide

-- …and the citation that is allowed: `G n` in a type position, which never
-- supplies `G` at runtime.
def b7cite : Term := prog{
  fn B7cite (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk b7cite = true := by native_decide

/-! ### B7b. Function bindings are comptime-moded

    A `fn` name may be capital and everything about it still works: it is
    declared, it is called, and the executing machine runs it — which is the
    whole content of "a function binding flips mode". `let F = Main` reaches a
    bare `fn` name directly (not only through a call `f(…)`), and the read
    succeeds because a capital binding reads its right-hand side by ⇝, which is
    not the rule that refuses reading a function out of its slot. -/

def b7capital : Term := prog{
  fn Bump (n : Nat) -> Nat { Add n 1 };
  fn Caller () -> Nat { Bump(1) };
  () }
example : progOk b7capital = true := by native_decide

def b7letF : Term := prog{
  fn Main () -> Nat { Add 1 1 };
  let F = Main;
  () }
example : progOk b7letF = true := by native_decide

-- Confirmation as a run rather than a static claim: a comptime-moded slot is
-- read by the executing machine as a plain slot read, no detour through the
-- normalizer — `Bump` still holds its runtime λ at the end and `y` is the value
-- the call computed.
def b7run : Term := prog{
  fn Bump (n : Nat) -> Nat { Add n 1 };
  let y = Bump(1);
  () }
example : progRuns b7run = true := by native_decide

/-! ### B8/B9. Borrow-typed binders must be lowercase — checked, not assumed

    Checked at both ends, with distinguishable rejections so the site is pinned
    rather than inferred: the declaration is caught where the signature is
    elaborated, and the call site is caught separately, which matters for a
    callee that was never itself checked. -/

def b8 : Term := prog_parse { fn B8 (V : &mut List Nat) -> Unit { () }; () }
example : progRejects b8 "telescope: parameter 'V' is capitalized" = true := by native_decide

def b9 : Term := prog_parse {
  fn B8 (V : &mut List Nat) -> Unit { () };
  fn Caller () -> Unit { let x = Cons(1, Nil); B8(&m x); () };
  () }
-- The needle is name-free: the callee's signature is a Π with no binder names,
-- so the call site synthesizes a name that encodes the mode (which is what the
-- rule needs) but not a display name. A synthesized name is as unstable as an
-- existential id, so pinning one to the message would rot.
example : progRejects b9 "is capitalized" = true := by native_decide

-- The lowercase twin of both, for liveness.
def b8lo : Term := prog{ fn B8lo (v : &mut List Nat) -> Unit { () }; () }
def b9lo : Term := prog{
  fn B8lo (v : &mut List Nat) -> Unit { () };
  fn Caller () -> Unit { let x = Cons(1, Nil); B8lo(&m x); () };
  () }
example : progOk b8lo = true := by native_decide
example : progOk b9lo = true := by native_decide

/-! ### B10. The reserved-keyword prescription

    Making capital the mode marker costs one rule: the constructor names are
    reserved keywords, checked at elaboration. A rejected macro produces no term
    to test, so what is asserted here is the other half — the surface no longer
    decides `F(x)` by case. `f(…)` is a constructor application exactly when `f`
    is in the fixed basis, which is what makes `G(n)` above (§B7) a call rather
    than a mistyped constructor application. -/

example : Surface.reservedBinder "Cons" = true := by native_decide
example : Surface.reservedBinder "Nat" = true := by native_decide
-- Lowercase names are NOT reserved: they were always shadowable, and reserving
-- common names like `k` would cost every program its loop indices for no
-- disambiguation at all.
example : Surface.reservedBinder "k" = false := by native_decide
example : Surface.reservedBinder "unit" = false := by native_decide
example : Surface.reservedBinder "Hfuel" = false := by native_decide

/-! ## §C. Capital `let` — the comptime binding, and what it actually buys

    `let X = e` evaluates `e` under ⇝, erases `X`, consumes nothing, and confines
    `X` to ⇝-positions. For a proof spine this changes nothing observable, since
    a spine already goes through the pure lift — so the payoff is in the one
    place a move and a read genuinely differ.

    **`*v` is a take under a move and a projection under ⇝.** `let l = *v` moves
    the payload out and leaves a hole; `let L = *v` reads the snapshot and leaves
    the borrow intact — a way to capture "the value `*v` holds right now" as a
    binding, without building a closure around the call first. -/

def c1 : Term := prog{
  fn C1 (v : &mut List Nat) -> Id (List Nat) (*v) (old *v) { let L = *v; Refl };
  () }
def c1bad : Term := prog_parse {
  fn C1bad (v : &mut List Nat) -> Id (List Nat) (*v) (old *v) { let l = *v; Refl };
  () }
example : progOk c1 = true := by native_decide
-- The runtime take leaves a hole in the borrow, and a hole satisfies no type.
-- Same program, one character — and the rejection names the hole, so this is
-- the take-vs-projection difference and not some other breakage.
example : progRejects c1bad "holds a hole (⊥) at return" = true := by native_decide

-- C2. The fence applies to a capital `let` exactly as to a capital parameter —
-- so the snapshot above is a specification binding, not a free copy of the data.
def c2 : Term := prog_parse { fn C2 (v : &mut List Nat) -> Unit { let L = *v; let y = L; () }; () }
example : progRejects c2 "cannot be ⇒-moved" = true := by native_decide

-- C3. The right-hand side must have a ⇝ reading. A call's result is a fresh
-- existential and has none, so a capital `let` cannot bind one — honest, and
-- pointing at the lowercase `let` that can.
def c3bad : Term := prog_parse {
  fn GiveLe (a : Nat) -> Le a a { LeReflRaw a };
  fn Caller (n : Nat) -> Unit { let P = GiveLe(n); () };
  () }
example : progRejects c3bad "not in the comptime fragment" = true := by native_decide

-- C4. Locally-derived certificates without staging: a capital `let` builds the
-- certificate, and citing it at capital argument positions never consumes it.
def c4 : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let Q = LeTransRaw n m m hnm (LeReflRaw m);
    UseLeC(n, m, Q); UseLeC(n, m, Q); hnm };
  () }
example : progOk c4 = true := by native_decide

/-! ## §D. Erased data — a distinction kind alone cannot express

    A capital `N : Nat` used only in types is erased at quantity 0. `Nat` is
    already index-kind and copies on read, but copy-on-read is not erasure — a
    copyable binder can still be branched on. The mode is what forbids that, and
    kind cannot derive it: the two binders below have the same kind and differ
    only in mode. -/

-- Accepted: `N` appears only in the return TYPE.
def d1 : Term := prog{ fn D1 (N : Nat) -> Id Nat N N { Refl }; () }
example : progOk d1 = true := by native_decide

-- Accepted: an erased length index, with the runtime data typed against it.
def d2 : Term := prog{
  fn D2 (N : Nat, l : List Nat, h : Id Nat (Len l) N) -> Id Nat (Len l) N { h };
  () }
example : progOk d2 = true := by native_decide

-- Fenced: the body tries to branch on it. Same type, same kind, same position as
-- §A5's `fuel` — only the case differs, and only the case can decide this.
def d3 : Term := prog_parse { fn D3 (N : Nat) -> Unit { match N { Z => (), S(k) => () } }; () }
example : progRejects d3 "cannot be the scrutinee of a runtime match" = true := by native_decide

/-! ## §E. Case is inert under ⇝ — pinned from both sides

    Two assertions that together say the modes are exactly as strong as
    intended and no stronger: the two Π's below are the same type to every
    comptime judgment, and a call still tells them apart. -/

-- E1. The mode is invisible to conversion…
example : Pure.convert 1000 ty{ Π (X : Nat) → Nat } ty{ Π (x : Nat) → Nat } = true := by native_decide
-- …and not erased by normalization, which is what leaves a call something to
-- read. (`==` is mode-blind, so this has to be asked structurally.)
example : (match Pure.nf 1000 ty{ Π (X : Nat) → Nat } with
           | .pi _ d _ => Term.domComptime d
           | _ => false) = true := by native_decide

-- E2. `Add` stays all-lowercase and is cited in a spec regardless — you never
-- capitalize a definition to use it in a type. Both cases of the citing
-- function's own binders work, because the citation happens under ⇝.
def e2lo : Term := prog{ fn E2lo (a : Nat, b : Nat) -> Id Nat (Add a b) (Add a b) { Refl }; () }
def e2hi : Term := prog{ fn E2hi (A : Nat, B : Nat) -> Id Nat (Add A B) (Add A B) { Refl }; () }
example : progOk e2lo = true := by native_decide
example : progOk e2hi = true := by native_decide

-- E3. The structured neutral is unchanged by the Π's binder case. An abstract
-- function applied twice in a type position is one term either way, which is
-- what `Refl` inhabiting the `Id` says.
def e3lo : Term := prog{ fn E3lo (f : Π (x : Nat) → Nat, a : Nat) -> Id Nat (f a) (f a) { Refl }; () }
def e3hi : Term := prog{ fn E3hi (f : Π (X : Nat) → Nat, a : Nat) -> Id Nat (f a) (f a) { Refl }; () }
example : progOk e3lo = true := by native_decide
example : progOk e3hi = true := by native_decide

/-! ### E4. The two equalities are asymmetric, deliberately

    `Term.convEq` is mode-blind because conversion is built on it and case is
    inert under ⇝. Structural `==` is not, because its clients are not
    conversions — an occurrence-abstraction pass, for instance, would wrongly
    match `⇝τ` against `τ` and abstract the marker away with the domain if `==`
    ignored it. Pinned because "one of these two is mode-blind and the other is
    not" is exactly the asymmetry a later reader would otherwise assume was an
    oversight. -/

example : (Term.convEq (.cmpT (.const "Nat")) (.const "Nat")) = true := by native_decide
example : ((Term.cmpT (.const "Nat") : Term) == Term.const "Nat") = false := by native_decide

/-! ## §F. Modes at a VALUE callee

    A recursor elaboration's induction hypothesis is a Π-typed *variable*, not a
    declaration's telescope — so the modes have to be readable off a Π that is a
    value, and the argument routing has to happen before the call's spine is
    consumed.

    Note what the pair below is *not* testing: typing a λ against a Π converts
    their domains, and conversion is mode-blind, so a λ written with lowercase
    binders can inhabit a capital-bindered Π. The mode that governs the call is
    therefore the one on the type the caller sees — the seal's ascription, not
    the λ's own binder names. F3 is that case on its own. -/

-- F1. A sealed callee with a capital binder: the argument is ⇝-read, so the
-- caller still holds its proof — twice over, and afterwards.
def f1 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- named so the closure's domain can cite them
    let G = (λ (H : Le N0 M0). Z : Π (H : Le N0 M0) → Nat);
    let r = G(hnm);
    let s = G(hnm);
    hnm };
  () }
example : progOk f1 = true := by native_decide

-- F2. The lowercase twin of the same seal: the call moves the proof.
def f2 : Term := prog_parse {
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- named so the closure's domain can cite them
    let G = (λ (h : Le N0 M0). Z : Π (h : Le N0 M0) → Nat);
    let r = G(hnm);
    hnm };
  () }
example : progRejects f2 "holds ⊥" = true := by native_decide

-- F3. The ascription is the contract. The same lowercase-bindered λ, sealed at
-- a capital-bindered Π: accepted (conversion is mode-blind), and the call takes
-- its argument by ⇝, because the caller's view is the Π and nothing else.
def f3 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- named so the closure's domain can cite them
    let G = (λ (h : Le N0 M0). Z : Π (H : Le N0 M0) → Nat);
    let r = G(hnm);
    let s = G(hnm);
    hnm };
  () }
example : progOk f3 = true := by native_decide

-- F4. The transparent case: a literal λ callee carries its modes on its own
-- domains, so the same routing happens with no seal in sight.
def f4 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- named so the λ's domain can cite them
    let G = λ (H : Le N0 M0). Z; let r = G(hnm); let s = G(hnm); hnm };
  () }
example : progOk f4 = true := by native_decide

-- F5. …and its lowercase twin moves, which is what says F4 is about the mode.
def f5 : Term := prog_parse {
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- named so the λ's domain can cite them
    let G = λ (h : Le N0 M0). Z; let r = G(hnm); let s = G(hnm); hnm };
  () }
example : progRejects f5 "holds ⊥" = true := by native_decide

/-! ## §G. What modes do not fix: a saturated call still cannot partially apply

    A residual λ/Π after a saturated spine is rejected, including the legitimate
    case of a function returning a function — and modes cannot distinguish the
    two. `Π (x : A) → (Π (y : B) → C)` and `Π (x : A) → Π (y : B) → C` are the
    same term: there is no residual binder whose mode belongs to one reading and
    not the other, since a binder's mode is a fact about how its own argument
    would be read, equally true under both readings. The mode decides runtime
    existence of a binder, not the shape of a return type.

    The separating fact is elsewhere: a residual telescope with no borrow-moded
    binder could in principle be curried soundly, since the reason for requiring
    saturation is that a partial application at runtime is a closure holding its
    arguments — including, in general, borrows. That is a separate design
    question, left open here. -/

-- A comptime λ's partial application is a value: the saturation requirement is
-- a rule about runtime call entry, and a comptime capture holds no borrow.
-- Saturation is still enforced where entry actually happens — see `g2`/`g3`
-- below.
def g1 : Term := prog_parse { let F = λ (x : Nat). λ (y : Nat). x; let z = F(2); () }
example : progOk g1 = true := by native_decide

-- The legitimate-return case, pinned as the limitation it is: `Mk` means to be
-- "the constant function at 1", and is refused.
def g2 : Term := prog_parse {
  let Mk = (λ (x : Nat). λ (y : Nat). x : Π (x : Nat) → Π (y : Nat) → Nat);
  let k1 = Mk(1); () }
example : progRejects g2 "partial application" = true := by native_decide

-- Modes ARE expressible on such a Π — the elaboration is fine, the marker is
-- there — and change nothing, which is the point.
def g3 : Term := prog_parse {
  let Mk = (λ (X : Nat). λ (y : Nat). X : Π (X : Nat) → Π (y : Nat) → Nat);
  let k1 = Mk(1); () }
example : progRejects g3 "partial application" = true := by native_decide

-- The route that does work today, so the limitation is bounded rather than
-- open-ended: a declared `fn` may return a function. It is only the
-- value-callee spine that cannot say "stop here and hand me the rest".
example : progOk S26Seal.a6c = true := by native_decide

/-! ## §H. The flagship — `quicksort (fuel, v, Hfuel)` reads right

    The intended signature: `fuel` lowercase (the body branches on it), `v`
    lowercase (a borrow), `Hfuel` capital (cited in certificates, never
    scrutinized, never consumed). `Hfuel` is passed to a call that also takes
    the borrow, and then cited afterwards — used to derive a certificate the
    body goes on to use. Without capital binders that sequence is unwritable
    without staging the proof into a closure before the call. -/

-- `step` is the callee of the flagship and of §H5/§H6; `stepLo` is H2's control,
-- the same callee with a runtime proof parameter instead. Each cohort below
-- declares its own copy of whichever one it calls.

-- H1/H2 together are a differential over the mode marker: `qsish` declares
-- `step` with a capital `H` and is accepted, because `Hfuel` is ⇝-read at the
-- call and so citing it afterwards is legal. `qsishLo` is the same body against
-- `stepLo`, whose proof parameter is lowercase, and is rejected as a move. So
-- this pair is exactly what would go red if a signature transformation ever
-- dropped the mode marker while preserving the binder count.
--
-- (H5 is a different check: its two halves are BOTH rejected, on purpose — it
-- is the evidence that staleness is not a mode problem, below.)

def qsish : Term := prog{
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn Qsish [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (Len *v) fuel) -> Unit
    { match fuel {
        Z => (),
        S(f2) => {
          Step(&m *v, S(f2), Hfuel);                       -- passed to a call…
          let Q = LeTransRaw (Len (old *v)) (S f2) (S f2) Hfuel (LeReflRaw (S f2));
                                                              -- …and cited afterwards
          UseLeC(Len (old *v), S(f2), Q);                     -- the derived certificate, used
          () } } };
  () }
example : progOk qsish = true := by native_decide

-- H2. The callee's declaration is what decides. The same body against
-- `stepLo`, whose proof parameter is lowercase: the call would move an erased
-- binder, and the fence says so. Which is the right division of labour — a
-- caller cannot know whether a callee needs its proof at runtime, so the
-- callee declares it.
def qsishLo : Term := prog_parse {
  fn StepLo (v : &mut List Nat, b : Nat, h : Le (Len *v) b) -> Unit { () };
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn QsishLo [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (Len *v) fuel) -> Unit
    { match fuel {
        Z => (),
        S(f2) => {
          StepLo(&m *v, S(f2), Hfuel);
          let Q = LeTransRaw (Len (old *v)) (S f2) (S f2) Hfuel (LeReflRaw (S f2));
          UseLeC(Len (old *v), S(f2), Q);
          () } } };
  () }
example : progRejects qsishLo "cannot be ⇒-moved" = true := by native_decide

-- H3. …and `Hfuel`'s neighbour cannot be scrutinized: an erased index is
-- erased, not merely copyable.
def qsishBad : Term := prog_parse {
  fn QsishBad (v : &mut List Nat, N : Nat, HN : Id Nat (Len *v) N) -> Unit
    { match N { Z => (), S(k) => () } };
  () }
example : progRejects qsishBad "cannot be the scrutinee of a runtime match" = true := by native_decide

-- H4. The exit/`old` machinery, unchanged by the presence of erased binders: an
-- erased length index, an erased proof about it, a comptime snapshot binding,
-- and a borrow, under a return type relating exit to entry.
def qsish2 : Term := prog{
  fn Qsish2 (v : &mut List Nat, N : Nat, HN : Id Nat (Len *v) N)
    -> Id (List Nat) (*v) (old *v)
    { let L = *v; Refl };
  () }
example : progOk qsish2 = true := by native_decide

/-! ### H5. What modes do NOT fix

    A bound stated about `*v` is invalidated by any call through `v`: the call
    re-mints the payload, so a second `step(&mut *v, …, Hfuel)` wants
    `Le (Len σ') …` where `Hfuel` still says `Le (Len σ_entry) …`. That is the
    borrow mechanism's opacity working as designed — the forgetting is
    wanted — and it is why a real quicksort derives a fresh bound per recursive
    call rather than reusing one.

    The pair below shows this is not a mode problem: capital and lowercase
    proof binders are refused identically, with the same message about the same
    parameter type. Modes fix proof consumption; they do not touch staleness. -/

def h5hi : Term := prog_parse {
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn H5hi (v : &mut List Nat, f : Nat, Hf : Le (Len *v) f) -> Unit
  { Step(&m *v, f, Hf); Step(&m *v, f, Hf); () };
  () }
def h5lo : Term := prog_parse {
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn H5lo (v : &mut List Nat, f : Nat, hf : Le (Len *v) f) -> Unit
  { Step(&m *v, f, hf); Step(&m *v, f, hf); () };
  () }
example : progRejects h5hi "does not have its parameter type" = true := by native_decide
example : progRejects h5lo "does not have its parameter type" = true := by native_decide

/-! ### H6. The fence's boundary: a comptime binder is not returnable

    A function's result is a moved value, so returning a capital binder is a
    move and the fence refuses it. Slightly surprising and entirely consistent —
    "usable only in ⇝-positions" includes the result position.

    The pair also shows which end the fix lives at. `h6lo`'s caller binder is
    runtime and it works: the callee's capital parameter is what stopped the
    consumption, so a caller that genuinely owns a proof may pass it and still
    return it. Capitalizing the caller's own binder is a claim about the
    caller's erasure, and a returned value is not erased. -/

def h6hi : Term := prog_parse {
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn H6hi (v : &mut List Nat, f : Nat, Hf : Le (Len *v) f) -> Le (Len (old *v)) f
  { Step(&m *v, f, Hf); Hf };
  () }
def h6lo : Term := prog{
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn H6lo (v : &mut List Nat, f : Nat, hf : Le (Len *v) f) -> Le (Len (old *v)) f
  { Step(&m *v, f, hf); hf };
  () }
example : progRejects h6hi "cannot be ⇒-moved" = true := by native_decide
example : progOk h6lo = true := by native_decide

/-! ## §I. Both machines, in lockstep

    The comptime-argument rule is taken by the executing machine too, so the two
    agree on the observable the differential compares: what the caller still
    holds after the call. Exercised at a concrete argument and at a symbolic one
    (a call's fresh existential), through a table call and through a value
    callee.

    The subject is a `List`, not a proof, deliberately: a `Nat` or a proof spine
    is index-kind and already copies on read, so it could not tell the two modes
    apart. A `List` moves under a runtime call, so a capital data binder being
    ⇝-read surfaces something worth naming: the callee gets the value and the
    caller keeps it — silent aggregate duplication, which is refused outright
    for lowercase binders. It is coherent only because the binder is erased
    (nothing is duplicated at runtime), and the fence is what makes that true,
    since the callee cannot observe it. The coherence rests on the fence, not on
    the read. -/

/-! `GiveL` (§I2 below) takes an argument it does not use, which is deliberate: a
    nullary function lowers to a runtime closure binding nothing, which the
    executing machine refuses (a thunk makes evaluation order ambiguous). A
    program declaring a nullary function would check but could not run, which
    would break I2's concrete side before the differential was even consulted.
    Taking one unused argument sidesteps this while still giving I2 what it
    needs: an argument that is a call's fresh existential rather than a literal.
    The nullary restriction itself is not tested here — that would only be a
    test of the executing machine refusing a thunk. -/

-- I1. Concrete: the capital call does not consume, so the list is still there.
def i1 : Term := prog{
  fn TakeLC (L : List Nat) -> Unit { () };
  let a = Cons(1, Nil); TakeLC(a); let b = a; () }
def i1lo : Term := prog_parse {
  fn TakeL (l : List Nat) -> Unit { () };
  let a = Cons(1, Nil); TakeL(a); let b = a; () }
example : progOk i1 = true := by native_decide
example : progRejects i1lo "holds ⊥" = true := by native_decide
-- …and the environment says so directly: `a` survived the call and was moved by
-- the `let b = a` that follows it. `tailEnv` drops the program's own function
-- bindings.
example : tailEnv i1 [("a", .bot), ("b", Val.cons (Val.nat 1) Val.nil)] = true := by
  native_decide

-- I2. Symbolic: the argument is a call's fresh existential rather than a literal.
def i2 : Term := prog{
  fn GiveL (u : Nat) -> List Nat { Cons(1, Nil) };
  fn TakeLC (L : List Nat) -> Unit { () };
  let a = GiveL(0); TakeLC(a); let b = a; () }
example : progOk i2 = true := by native_decide

-- I3. Through a value callee, transparent and sealed.
def i3 : Term := prog_parse {
  let a = Cons(1, Nil); let G = λ (L : List Nat). Z; let r = G(a); let b = a; () }
def i3s : Term := prog{
  let a = Cons(1, Nil); let G = (λ (L : List Nat). Z : Π (L : List Nat) → Nat);
  let r = G(a); let b = a; () }
example : progOk i3 = true := by native_decide
example : progOk i3s = true := by native_decide

-- The differential: the executing machine reaches the same final state. `diffC`
-- relates a checking-side environment to an executing-side one up to
-- existential-instantiation and the pure fragment's own computation.
--
-- Each shape is now a whole program, so it declares its own callee inline. The
-- function binding shows up in both final environments — sealed (an
-- existential) on the checking side, the actual closure on the executing side —
-- and the relation binds the one to the other.
def shapes : List Term := [i1, i2, i3, i3s]
example : shapes.all diffC = true := by native_decide

end Dllbc.Tests.S26Modes
end

section
/-!
# The mixed-return-type containment

A borrow-carrying return type is audited structurally: the checker walks it and
checks each issued borrow against its owed type. That audit gates the value check
on the WHOLE return type being borrow-free, so a non-borrow component sitting
alongside a borrow component in the same return type was judged by nothing at
all — a caller could receive an unearned proof through it and return the proof at
its own, correctly-checked, value return type.

**The containment.** Refuse a return type that mixes borrow and non-borrow
components, at both dispatch sites (the declaration path and the sealed-λ path),
rather than teach the audit to judge value components in a borrow-carrying
position. A cursor's sayable contract is its issued borrows' owed types; a value
claim belongs on a value-returning function, where the check actually looks.

**The containment has since been repealed.** The audit now judges a mixed
return's value components directly — opened at the actual borrow components,
against the return type pinned at entry — so the dishonest case below is caught
by the check itself and its honest twin is accepted. The flips are recorded at
their sites below.
-/

open Dllbc
open Dllbc.StdChainRaw (ZnotsRaw)

namespace Dllbc.Tests.S27Mixed

/-! ## §A. The break, contained — a false claim beside an issued borrow

    `a1lie` is a cursor returning the head borrow beside a false claim
    (`Id Nat Z (S Z)`) discharged by a `Refl` that cannot inhabit it. -/

def a1lie : Term := prog_parse {
  fn HeadLie (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat). Id Nat Z (S Z)
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&m *hd, Refl)
        } };
  () }

-- The refusal is now by judgment rather than by position: the audit judges
-- value components of a mixed return (opened at the actual borrow component,
-- against the entry-pinned type), so the lie is caught by the check itself —
-- `Refl` cannot inhabit `Id Z (S Z)` — rather than the position being
-- unwritable.
example : progRejects a1lie "mixed return type — value component" = true := by native_decide

/-- The honest twin of `a1lie`, and the flip that says the position is judged
    now rather than refused outright: the audit opens the tail at the actual
    borrow component and checks the value component against it, so this true
    claim is accepted and the lie above is refused, each by the same look. -/
def a5honest : Term := prog{
  fn HeadTrue (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat). Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&m *hd, Refl) } };
  () }

example : progOk a5honest = true := by native_decide

/-! ## §B. The two controls that isolate the mixed return type as the whole cause

    Neither changes here, and that is the point: the containment touches only
    the mixed position, so the rules that were already looking are left exactly
    as they were. -/

-- A2: the SAME false claim with no borrow in the return type. The pin-and-check
-- path runs, and always did.
def a2lie : Term := prog_parse {
  fn ValLie (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : Nat). Id Nat Z (S Z)
        { Pair(Z, Refl) };
  () }
example : progRejects a2lie "does not have return type" = true := by native_decide

-- A5a: the direct route to the same absurdity, refused as it always was.
def a5direct : Term := prog_parse {
  fn Direct () -> Bot { ZnotsRaw Z Refl };
  () }
example : progRejects a5direct "does not have return type" = true := by native_decide

/-! ## §C. Not over-broad: the shapes the corpus actually uses still check

    A containment that refused real cursors would be a regression wearing a
    fix's clothes. The two live shapes are a bare borrow and a Σ of borrows, and
    both are all-borrow, so neither mixes. -/

def bare : Term := prog{
  fn Bare (v : &mut List Nat, hi : Le (S Z) (Len *v)) -> &mut Nat
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &m *hd } };
  () }
example : progOk bare = true := by native_decide

def twoBorrows : Term := prog{
  fn Two (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat). &mut List Nat
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&m *hd, &m *tl)
        } };
  () }
example : progOk twoBorrows = true := by native_decide

-- …and the whole corpus is unmoved: the full suite is green with the refusal
-- in, which is the claim the fix has to earn — it must catch the break without
-- catching a single thing the corpus already relies on.

/-! ## §D. The sealed-λ path has the same hole

    A sealed λ's return type ascription gates its value check the same way a
    declaration's does, so a sealed λ ascribed at a mixed Π was unjudged in the
    same way and needed the same fix. -/

def mixedSeal : Term := prog_parse { Π (v : &mut List Nat) → Σ (x : &mut Nat). Id Nat Z (S Z) }

def sealProg : Term := prog_parse {
  let F = (λ(v : &mut List Nat) { match v { Nil => (), Cons(hd, tl) => Pair(&m *hd, Refl) } } : mixedSeal);
  () }

-- The program is still refused, though for an earlier reason: its `Nil` branch
-- returns `()` against the mixed Σ, which routes it to the value-return path,
-- and reading a borrow-carrying type as pure data refuses by name before the
-- mixed value-component check ever runs. The false claim in the `Cons` branch
-- would be caught by that check if the program got that far; the earlier
-- refusal wins the race.
example : progRejects sealProg "only valid at a telescope position" = true := by native_decide

-- Not vacuous: an all-borrow ascription in the same position is accepted, so the
-- refusal is about the MIXTURE and not about sealing a cursor at all.
def borrowSeal : Term := prog_parse { Π (v : &mut List Nat) → &mut List Nat }
def sealOk : Term := prog{ let F = (λ(v : &mut List Nat) { v } : borrowSeal); () }
example : progOk sealOk = true := by native_decide

/-! ## §E. A second containment — a lie in a parameter's owed type

    A second unsound case sits inside the first containment's blessing: the
    return type here is all-borrow, so §A's refusal has nothing to say about
    it. The lie hides one level down, in what the parameter owes back.

    A borrow consumed into the result is exempt from the payload audit — a
    borrow that left in the result has no payload here to check. But the
    exemption takes the owed type with it, and the caller's group-end then
    mints the captured loan's release at that type — so the callee is excused
    from proving the claim and the caller receives it as fact. Neither end
    looks.

    **Refused rather than repaired**, on the same reasoning as §A: "check the
    release against the owed type" is vacuous as stated, since a freshly minted
    existential trivially has the type it was minted at. Making the unjudged
    position unwritable is the honest move. A parameter passed onward into the
    result owes back the type it was lent. -/

def e1lie : Term := prog_parse {
  fn ThroughLie (v : &mut (s : List Nat ~> Id Nat Z (S Z))) -> &mut List Nat
        { v };
  () }
example : progRejects e1lie "would be checked by nobody" = true := by native_decide

/-- The isolating control: the same body and the same consumed-into-result shape
    with a trivial owed type is accepted. So the refusal is about the claim, not
    about handing a borrow onward, which is `ThroughOk`'s whole job. -/
def e2trivial : Term := prog{
  fn ThroughOk (v : &mut List Nat) -> &mut List Nat { v };
  () }
example : progOk e2trivial = true := by native_decide

/-! ### E3. The corpus's non-trivial owed types

    A refusal that caught a load-bearing owed type would be a design
    conversation rather than a containment. Across the corpus, only two borrow
    parameters carry a non-trivial owed type, and both are Unit-returning, so
    neither is ever consumed into a result and the exemption cannot fire on
    them — their owed types are checked. That is the whole reason this ships as
    a containment: the position it closes is one the corpus never used. -/

-- `to_nat (v : &mut (Bool ~> Nat))` — the type-changing ↝, S6Call's own subject.
example : progOk Tests.S6Call.toNatProg = true := by native_decide

/-! ### `swapS01` — the other rich owed type

    A spec-carrying in-place swap of positions 0 and 1, its ↝-obligation the Σ
    `Σ (l : List Nat). Id Nat (Len l) (Len s)`. The cursor work stays inside one
    body: the entry proof `LenSwapLRaw 0 1 (*v)` is captured non-destructively; the
    two element cursors (one from `v`, one from its tail, disjoint by
    construction) swap by take-and-fill; `let l = *v` collapses the field loans
    transparently to the swapped list; `*v := Pair(l, proof)` fills the Σ. The
    proof's type refines with the match, and the cursor output converges with
    `SwapL 0 1 s` by computation, so it type-checks against `Id (Len l) (Len s)`
    — the cursor writes and the pure specification agree. -/

/-- `swapS01` as a prefix: it is the callee of everything below, and the caller is
    a plain statement block, so the idiom applies — a Lean function taking the
    rest and splicing it with `%`. -/
def withSwapS01 (rest : Term) : Term := prog{
  fn SwapS01 (v : &mut (s : List Nat ~> Σ (l : List Nat). Id Nat (Len l) (Len s)),
                    p : Le 2 (Len (*v))) -> Unit {
    let proof = StdChainRaw.LenSwapLRaw 0 1 (*v);
    match v {
      Nil => botElim Unit p,
      Cons(h0, t0) => {
        match t0 {
          Nil => botElim Unit p,
          Cons(h1, t1) => {
            let tmp = *h0;
            *h0 := *h1;
            *h1 := tmp;
            let l = *v;
            *v := Pair(l, proof);
            ()
          }
        }
      }
    }
  };
  rest }

/-- The declaration alone, checked at its seal. -/
def swapS01 : Term := withSwapS01 prog_parse { () }
example : progOk swapS01 = true := by native_decide

-- Caller: borrow, call SwapS01, demand the owner (recovering the Σ), open it to
-- l + the carried proof `pf : Id (Len l) (Len [1,2,3])`. The evidence survives the
-- opaque group-end — pf is in scope downstream though l itself is opaque.
def swapCaller : Term := withSwapS01 prog_parse {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  SwapS01(b, ());
  let Pair(l, pf) = x;
  let m = l; () }

example : progOk swapCaller = true := by native_decide
-- The proof survives to the final env (pf ↦ a σ : Id (len l) (len [1,2,3])).
example : (match tailEnvs swapCaller with
  | [.ok env] => (env.lookup "pf").isSome
  | _ => false) = true := by native_decide

/-! ## §F. Reading a sealed borrow-taking function into a second binding

    A sealed function whose Π is borrow-moded has no ordinary value form, so
    reading it into a second binding without care could produce a program
    **both machines accept** whose final states do not correspond: the checking
    side sees the binding as erased (`⊥`), the executing side holds the real
    closure. That is a simulation break on an accepted program, exactly what the
    differential exists to catch.

    **The fix is now a mode, not a special case.** A function binding is
    comptime: `let F = …` is ⇝-read, erased, and never move-consumed, so
    `let G = F` copies knowledge, leaves `F` where it was, and creates no second
    owner for the two machines to disagree about. What is still refused is the
    lowercase destination — `let g = F` moves an erased binder and is refused by
    the ordinary fence, while `let G = F` is accepted. -/

def fSeal : Term := prog_parse { Π (v : &mut List Nat) → Unit }

-- F1. A sealed borrow-taking function bound to a second, lowercase slot: refused,
-- since binding a function is comptime and the destination must be too.
def f1read : Term := prog_parse {
  let F = (λ(v : &mut List Nat) { () } : fSeal);
  let g = F;
  () }
example : progRejects f1read "the binder to capitalise is the destination" = true := by
  native_decide

-- The fix: capitalise the second binder and the program is fine. No divergence
-- between the machines can arise from it, because a comptime binding is not a
-- second owner — nothing was moved.
def f1readCap : Term := prog{
  let F = (λ(v : &mut List Nat) { () } : fSeal);
  let G = F;
  () }
example : progOk f1readCap = true := by native_decide

-- F2. The same refusal for a borrow-FREE sealed function: functions are
-- comptime-moded regardless of whether their domain happens to hold a borrow, so
-- the refusal here is the same one F1 gets.
def gSeal : Term := prog_parse { Π (x : Nat) → Nat }
def f2read : Term := prog_parse {
  let F = (λ(x : Nat) { x } : gSeal);
  let g = F;
  () }
example : progRejects f2read "the binder to capitalise is the destination" = true := by
  native_decide

-- F2b. The isolating control: an ordinary value in a second slot is still an
-- ordinary read. So F1/F2 are about functions and not about second bindings.
def f2data : Term := prog_parse {
  let f = 3;
  let g = f;
  () }
example : progOk f2data = true := by native_decide

-- F3. And it does not touch calling, which is a name-use rather than a read: a
-- call locates its callee rather than moving it, so it never reaches the read
-- rule at all.
def f3call : Term := prog{
  let F = (λ(v : &mut List Nat) { () } : fSeal);
  let x = Cons(1, Nil);
  let b = &m x;
  F(b);
  () }
example : progOk f3call = true := by native_decide

end Dllbc.Tests.S27Mixed
end

section
/-!
# Fuel-threading: paying for a recursion with no structural recursor form

A recursion that shrinks a borrow's payload (rather than an ordinary structural
argument) has no recursor form until a borrow-mode eliminator exists, so the
interim is to thread an explicit fuel parameter that decreases instead. This
file pays that price for a few different shapes, so that "the interim is
available" is a measured claim per shape rather than an extrapolation from one.
Each pair is a twin: the original stays exactly as it is, and the fuel-threaded
migration is legible as a diff against it.

**What each section reports is the price.** The interim was chosen knowing the
surface cost; what was not known ahead of time was whether the cost is uniform
across shapes, and it is not — the list cursor costs a parameter and a dead
branch, and the array cursor costs something else (§B).
-/

open Dllbc

namespace Dllbc.Tests.S26Fuel

/-! ## §A. The list cursor: `zero_all`

    `zero_all` walks a list through a mutable borrow, zeroing each element, and
    passes the tail's field reborrow to itself. It is the shape with no
    structural counter at all. -/

def zeroAllF : Term := prog{
  fn ZeroAllF [fuel] (fuel : Nat, v : &mut List Nat, Hf : Le (Len *v) fuel) -> Unit {
    match v {
      Nil => (),
      -- The dead branch: `Hf : Le (S (Len *tl)) Z` IS `Bot`.
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => { *hd := 0; ZeroAllF(f2, tl, Hf); () }
      }
    } };
  () }

example : progOk zeroAllF = true := by native_decide
-- The original recursion on the borrow alone, with no fuel parameter, is
-- rejected: `S6Call.zeroAll` is a program that declines with `progOk = false`,
-- since it has no recursor form to elaborate against.

/-! ## §B. The array cursor was already paid, and the corpus says so

    `walkArr [a]` recurses on a carved sub-slice, which is rejected: comparing the
    actual argument against the parameter's current snapshot only sees a
    structural predecessor along an unrefined spine, and carving a sub-slice
    refines the payload beyond what that comparison can follow. So array
    recursion needs fuel-threading too, and there is nothing to migrate: `walk`
    IS `walkArr` with `[fuel]` in place of `[a]` and the same body
    character-for-character, and it already checks. The array shape's price was
    paid before this question was even posed.

    So the declaration path rejects `walkArr` at the guard, the macro declines it
    at `[a]`-on-a-borrow, and the two reasons are the same fact seen from two
    sides — both verdicts are asserted where the two functions are written. -/

/-! ## §C. Most of the class needing fuel does not actually need it

    A recursion hint like `[k]` merely selects which parameter the checker
    watches for structural decrease; it is not itself what licenses the
    recursion. `NthL`/`nth2` name the borrow they recurse on, but they ALSO
    decrease on their index, which is a plain `Nat` — so correcting the hint to
    point at the index costs nothing: no fuel, no signature change, no caller
    change, no dead branch, the same body and the same return type, with only the
    hint different. The bound descends definitionally exactly as it did.

    With the hint corrected the whole `NthL`/`nth2` family migrates cleanly: every
    member that used to decline now checks (or rejects, for the one negative
    control that is meant to). What genuinely needs fuel is narrower than it
    first looks: a cursor with no decreasing argument of its own beyond the
    borrow itself (`zero_all`, and `recCursor`, which is the same shape under
    another name).

    `NthL`/`nth2` now declare the corrected hint at their own source, so what this
    section pins is the finding rather than a diff: the declaration path is as
    happy with an index hint as it was with a borrow hint (a structural descent
    accepts either), which is legible directly in the source that declares
    `[i]`. -/

/-! Every corrected member of the family checks except the one negative control,
    which still rejects. Nothing in the family declines any more. -/

/-! ## §D. What is left needing fuel, and one thing that looks like a macro gap

    After §B and §C, what still needs fuel is: a cursor with no decreasing
    argument but the borrow's own payload (`zero_all`/`recCursor`), plus the
    handful of cursors blocked by a declared `back` mechanism rather than by a
    hint. Correcting a hint is free; removing a `back` is a separate design
    question that changes what a caller can rely on.

    One thing that looks like a macro gap and is not: eliding the recursion hint
    entirely makes the macro emit a plain sealed λ without checking that the body
    has no self-call, so `zero_all` with its hint removed elaborates happily. The
    resulting program is still rejected, and by the ordinary scoping mechanism —
    the `let` is not in scope in its own right-hand side, so the self-call
    resolves to nothing and falls through as an unwritable forward reference. A
    macro-level refusal here would only paper over that demonstration. -/

-- `zero_all` with its recursion hint removed, as a program.
-- The same function WITH the hint, accepted below as `zeroAllF`; the two sit
-- either side of the distinction this section is about.
def noHintStmt : Term := prog_parse {
  fn ZeroAll (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ZeroAll(tl); () } } };
  () }
example : progRejects noHintStmt "unknown function" = true := by native_decide
-- Not vacuous: the same body WITH a hint (and the fuel §A threads) is a program
-- that checks, so the rejection above is about the missing recursor and not about
-- the body.
example : progOk zeroAllF = true := by native_decide

end Dllbc.Tests.S26Fuel
end

section
/-!
# Programs as terms

**A program is an arbitrary term, and running it is evaluating it.** A module is
a let-chain — transparent lets, sealed lets, a tail — and checking it is the
symbolic walk of the same term. There is no separate function-declaration form:
a `fn` is sugar for a sealed `let` of a λ.

Three claims are tested here:

  1. **The walk is the check.** Checking a program is exploring it plus auditing
     each path's result; each sealed `let` fires its audit once, at its own
     node, in program order.
  2. **Scope is the call table.** A callee is a binding lexically above the
     call, so a program is checked against no separate table, and a forward
     reference is unwritable rather than rejected — a let-chain cannot
     reference downward.
  3. **A body's free variables are its callees.** With no table, a runtime
     closure's callees are ordinary free variables: admitted when they name a
     function bound above, refused otherwise (capturing data or borrows stays
     refused). Both machines need this: the checking side seeds admitted
     bindings through frame isolation, the executing side keeps their ids out
     of the frame shift.

**Both machines, every program.** Each program below is checked and run, and the
differential is asserted on it, so a checking-side claim never stands for a
program that was never run.
-/

open Dllbc
open Dllbc.StdChainRaw (LeReflRaw LeUpRRaw)

namespace Dllbc.Tests.S26Prog

/-! ## Helpers

    `progOk`/`progRejects`/`runProgram` are `Program.lean`'s. The differential
    is the same merged relation used elsewhere, applied to a whole program
    instead of a single function body — it already took a term, so nothing new
    was needed for that. -/

open Dllbc.Tests.S9Diff (progDiff)

/-- The walk WITHOUT the end-of-scope demand — for showing that `endScope` is not
    vacuous (it is the difference between a parked loan and a released value). -/
def rawEnvs (t : Term) : List (Except String Env) :=
  (explore defaultFuel (atBoundary t) initSt).map
    (fun r => r.map (fun p => canonicalize p.2.env))

/-! ## §A. A program is a term

    The smallest complete statement of this: no declaration form, no telescope,
    no return type to declare separately — a let-chain and a tail, checked by
    one walk and run by the other. -/

-- A1. Transparent lets and a tail. The tail is checked in the accumulated
-- state, which is what makes the return type a real demand site rather than
-- decoration.
def a1 : Term := prog_parse { let x = 3; let y = S(x); y }
example : progOk a1 ty{ Nat } = true := by native_decide
example : progRejects a1 "does not have return type" ty{ Bool } = true := by native_decide
-- `x` survives its own use: a `Nat` is index-kind, so copy-on-read leaves the
-- owner intact where data proper would be moved out.
example : progRunsTo a1 [("x", Val.nat 3), ("y", Val.nat 4)] = true := by native_decide
example : progDiff a1 = true := by native_decide

-- A2. A sealed `let` is a definition, and the next binding calls it. Two things
-- at once: the seal's audit fires at its own node, and the call resolves to a
-- BINDING rather than to a table entry.
def a2 : Term := prog{
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let G = (λ(y : Nat){ F(y) } : Π (y : Nat) → Nat);
  let r = G(3);
  r }
example : progOk a2 ty{ Nat } = true := by native_decide
example : progDiff a2 = true := by native_decide
-- The claim that it was really the seal that made `f` callable: the same program
-- with `f` bound to a NON-function is refused, and the refusal names the capture.
def a2cap : Term := prog_parse {
  let f = 3;
  let G = (λ(y : Nat){ let z = f; y } : Π (y : Nat) → Nat);
  () }
example : progRejects a2cap "a runtime (lowercase) binding" = true := by native_decide

-- A3. A sealed function that MUTATES through a borrow, applied to a local. The
-- program owns the list, lends it, and gets it back — the whole borrow story with
-- no declaration anywhere in it.
def push : Term := prog{
  let Push = (λ(e : Nat, v : &mut (s : List Nat ~> List Nat)){
                    let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut (s : List Nat ~> List Nat)) → Unit);
  let l = Cons(1, Nil);
  let r = Push(7, &m l);
  () }
example : progOk push = true := by native_decide
-- The list really was mutated through the borrow, and the borrow really did come
-- back: `l` holds the pushed list, not a hole and not a parked loan.
example : (match runProgram push with
           | .ok env => (env.lookup "l" == some (Val.cons (Val.nat 7) (Val.cons (Val.nat 1) Val.nil)))
           | .error _ => false) = true := by native_decide
example : progDiff push = true := by native_decide

/-! ## §B. Each sealed `let` fires its audit once, at its own node, in program order

    Taken apart into the three things it claims. The audit is at the binding
    (not at a use), it happens whether or not there is a use, and the order the
    lets are written is the order the audits run. -/

-- B1. A sealed function that does not inhabit its ascription is refused at its
-- own `let`, with nothing downstream of it — the binding is the demand site.
def b1 : Term := prog_parse { let F = (λ(x : Nat){ x } : Π (x : Nat) → Bool); () }
example : progRejects b1 "does not have return type (Bool)" = true := by native_decide

/-- ### B2. The vacuous twin, kept beside it

    An unsealed λ with the same nonsense body is accepted, because nothing
    demands it: forming a λ value never looks inside its body. This is the trap
    a reader of B1 would otherwise fall into — "binding a bad function is
    caught" is true only of a sealed binding. The live twin below is what makes
    it a real difference: call it, and the demand arrives. -/
def b2vac : Term := prog{ let G = λ(x : Nat){ True }; () }
def b2live : Term := prog{ let G = λ(x : Nat){ True }; let r = G(1); r }
example : progOk b2vac = true := by native_decide
example : progRejects b2live "does not have return type (Nat)" ty{ Nat } = true := by native_decide

-- B3. Program order, pinned the only way it can be: two lies, and the one that
-- is reported is the first. (Both messages have the same shape, so the needles
-- are the types, which differ.)
def b3 : Term := prog_parse {
  let F = (λ(x : Nat){ x } : Π (x : Nat) → Bool);
  let G = (λ(x : Nat){ True } : Π (x : Nat) → Unit);
  () }
example : progRejects b3 "does not have return type (Bool)" = true := by native_decide
example : progRejects b3 "does not have return type (Unit)" = false := by native_decide

/-! ## §C. Scope is the call table

    A caller sees exactly the bindings lexically above it, so there is no
    separate callee-resolution table to assemble. Every program in this file is
    checked against an empty table, which is the positive half of that claim.
    Here is the rest. -/

/-- ### C1. No forward references — unwritable, not rejected

    A let-chain cannot reference downward, so `H` in `G`'s body does not resolve
    to the `H` bound below: it resolves to nothing at all. Nothing implements
    this rule specially — it is what scope IS, which is why mutual recursion is
    unwritable rather than rejected by a check. Note WHERE it is caught: at
    `G`'s own seal, because the audit is at the binding, so the diagnosis does
    not wait for a call. -/
def c1 : Term := prog_parse {
  let G = (λ(y : Nat){ H(y) } : Π (y : Nat) → Nat);
  let H = (λ (x : Nat). x : Π (x : Nat) → Nat);
  () }
example : progRejects c1 "unknown function 'H'" = true := by native_decide
-- …and the same program with the two bindings swapped is accepted, so the
-- rejection is about the order and not about the pair.
def c1ok : Term := prog{
  let H = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let G = (λ(y : Nat){ H(y) } : Π (y : Nat) → Nat);
  let r = G(3);
  r }
example : progOk c1ok ty{ Nat } = true := by native_decide
example : progDiff c1ok = true := by native_decide

/-! ### C2. What a caller keeps is exactly what the callee's seal ascribes

    Guarding caller-side reasoning here is one program under two signatures: the
    callee's body and the caller that uses it are identical and honest in both,
    and what differs is only the type the body is sealed at. What the caller
    keeps is what the programmer wrote at the seal — and the sealed-but-weaker
    signature below is itself a program that checks, since the lie is not in
    the callee's body but in what its seal promises. -/

/-- The whole program, parameterised by the ONE thing the pair differs in. Body
    and caller are shared by construction rather than by two copies agreeing, so
    the difference the test measures is the only difference there is. -/
def c2under (sig : Term) : Term := prog{
  let F = (λ(n : Nat){ Pair(n, Refl) } : sig);
  let r = F(3);
  r }
/-- The retType the program is demanded at: the equation the caller wants. -/
def c2demand : Term := prog_parse { Σ (m : Nat). Id Nat m 3 }

/-- A — the signature carries the equation. -/
def c2keeps : Term := c2under (prog_parse { Π (n : Nat) → Σ (m : Nat). Id Nat m n })
/-- B — the same body, sealed at a type that forgets it (true, and useless). It
    checks: the lie is not in the callee, it is in what the callee promises. -/
def c2forgets : Term := c2under (prog_parse { Π (n : Nat) → Σ (m : Nat). Id Nat m m })

example : progOk c2keeps c2demand = true := by native_decide
example : progRejects c2forgets "does not have return type" c2demand = true := by native_decide
-- Not vacuous: the forgetting prefix is a program that checks on its own
-- terms — at the weaker demand its callee's signature does support. So the
-- rejection above is about what was kept across the seal, not about the
-- program being broken.
example : progOk c2forgets (prog_parse { Σ (m : Nat). Id Nat m m }) = true := by native_decide
-- The keeping prefix does NOT also satisfy the weaker demand: there is no
-- subsumption here, only conversion — an existential has the type it was
-- minted at, and `Id Nat m 3` and `Id Nat m m` are different types even though
-- the first is the more informative claim about this particular callee.
example : progOk c2keeps (prog_parse { Σ (m : Nat). Id Nat m m }) = false := by native_decide

/-! ## §D. Globals: the one kernel rule this needed

    A runtime closure's body was required to be closed over its own binders and
    globals, and until now "globals" was empty, because callees lived in a
    separate table. Putting callees in scope means a body's free variables ARE
    its callees, and the closedness premise had to learn the
    difference between naming a function above you and capturing your
    environment. The line is drawn at what the body can DO with the binding: a
    function is called (a place read — the callee is located, never moved),
    while data is moved, borrowed, or written.

    Both machines needed something, and neither needed the other's: the checking
    side seeds the admitted bindings through frame isolation (a sealed body's
    state is otherwise fresh), the executing side keeps their ids out of the
    frame shift so a reference still finds its binding inside a nested frame. -/

-- D1. Two frames deep: `H` calls `G` calls `F`, each a binding above it. This is
-- what says the keep set survives NESTING — the innermost body is entered through
-- two frame shifts, and both globals are still where the program put them.
def d1 : Term := prog{
  let F = (λ (x : Nat). S(x) : Π (x : Nat) → Nat);
  let G = (λ(y : Nat){ F(F(y)) } : Π (y : Nat) → Nat);
  let H = (λ(z : Nat){ G(G(z)) } : Π (z : Nat) → Nat);
  let r = H(0);
  r }
example : progOk d1 ty{ Nat } = true := by native_decide
-- The executing machine agrees, and on the VALUE: four applications of successor.
example : (match runProgram d1 with
           | .ok env => env.lookup "r" == some (Val.nat 4)
           | .error _ => false) = true := by native_decide
example : progDiff d1 = true := by native_decide

/-- ### D2. What is still refused, per capture kind

    Environment capture stays refused wholesale: admitting functions is not
    admitting environments. Each refusal is paired with the same program passing
    the thing in as an ordinary parameter instead, so the rejection is about the
    capture and not about the program. -/

-- D2a. Data. The message names a binding in scope and says that binding is not
-- a function.
def d2data : Term := prog_parse {
  let n = 3;
  let G = (λ(a : Nat){ let z = n; a } : Π (a : Nat) → Nat);
  () }
def d2dataOk : Term := prog{
  let n = 3;
  let G = (λ(a : Nat, m : Nat){ let z = m; a } : Π (a : Nat) → Π (m : Nat) → Nat);
  let r = G(1, n);
  r }
example : progRejects d2data "a runtime (lowercase) binding" = true := by native_decide
example : progOk d2dataOk ty{ Nat } = true := by native_decide

-- D2b. A borrow — the case this rule is really about, since a captured borrow
-- is a suspended loan with no scope to end it in.
def d2borrow : Term := prog_parse {
  let l = Cons(1, Nil);
  let b = &m l;
  let G = (λ(a : Nat){ *b := Nil; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d2borrow "a runtime (lowercase) binding" = true := by native_decide

-- D2c. A free variable that names nothing is a different rejection with a
-- different message. Under one `var` (docs/22) it is the BOUNDARY's: a name
-- nothing in the program binds is refused before any rule runs, so the
-- let-chain's "cannot reference downward" (`admitGlobals`) is never reached
-- by a program with a free name — it still guards the λ's CAPTURE of names
-- that are bound, which D2a/D2b above exercise.
def d2free : Term :=
  .seq (.letIn (Var.slot "g") (.seal 0 (Term.lamTel [(Var.slot "a", .const "Nat")]
      (.seq (.letIn (Var.slot "z") (.var "nope")) (.var "a")))
    (prog_parse { Π (a : Nat) → Nat }))) .unit
example : progRejects d2free "unbound identifier 'nope'" = true := by native_decide

-- D3. A sealed proof is not a global either, and that is deliberate rather than
-- an oversight: a body that wants it should take it as a capital parameter
-- instead. Recorded as a limitation with its route beside it, not as a defect.
def d3 : Term := prog_parse {
  let cert = (LeReflRaw 3 : Le 3 3);
  let G = (λ(a : Nat){ let z = cert; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d3 "a runtime (lowercase) binding" = true := by native_decide

-- D3b. The capital form of the same binding is accepted, and this test is the
-- clearest statement of why. A capital `let` is ⇝-read even when sealed
-- (minting the existential still happens, but the seal's own event is what a
-- capital binding reads), so a capital `let` of a proof is not a special case —
-- it is the ordinary rule.
--
-- This is not a concession made for proofs; it is forced. `fn F …` desugars to
-- exactly this term — a comptime `let` of a λ ascribed its Π — so a rule that
-- refused a capital seal of a proof would refuse every function declaration in
-- the language. A `Qed`-style proof binding and a function declaration are the
-- same form under the hood, so the same answer covers both.
--
-- D3 above is unmoved, but note WHY: D3's `cert` is refused for being
-- lowercase — the citation rule reading the binder's mode — not because proofs
-- specifically cannot be bound. Under the rule as it now stands a proof bound
-- capital IS citable from inside a body, and D3c below pins that rather than
-- leaving it to be inferred from this paragraph.
def d3cap : Term := prog{ let C = (LeReflRaw 3 : Le 3 3); () }
example : progOk d3cap = true := by native_decide

-- D3c. The citation half, which D3/D3b together imply and neither checks: the
-- capital proof cited from inside a λ body, at a ⇝ position. Accepted, since a
-- capital binder is always citable regardless of what value it holds.
def d3cite : Term := prog{
  let C = (LeReflRaw 3 : Le 3 3);
  let G = (λ(a : Nat){ LeUpRRaw 3 3 C } : Π (a : Nat) → Le 3 (S 3));
  () }
example : progOk d3cite = true := by native_decide

-- And the moving half is still shut, which is why "citable" is not "usable
-- anywhere": `let z = C` inside the body moves a comptime binder, and the fence
-- takes it before the citation rule is even consulted. Capture is open;
-- consumption is not.
def d3move : Term := prog_parse {
  let C = (LeReflRaw 3 : Le 3 3);
  let G = (λ(a : Nat){ let z = C; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d3move "cannot be ⇒-moved" = true := by native_decide

/-! ## §E. The end of a program is a demand on everything it still holds

    A program that lends a local and never looks at it again leaves the loan
    parked: the checking machine releases a group only when something demands
    it, and nothing does on its own. The executing machine releases a frame's
    loans on the way out. Without an end-of-program demand the two would end in
    visibly different final states on an ordinary program — so this is not
    tidiness, it is the differential's precondition, shown here as a difference
    rather than merely asserted. -/

-- E1. The raw walk leaves the loan parked…
example : (rawEnvs push).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .loanM _ => true | _ => false)
    | .error _ => false) = true := by native_decide
-- …and the ended one has released it into an existential, which the concrete
-- list then instantiates (that is why §A's `progDiff push` is green).
example : (programEnvs push).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => v.symOf?.isSome)
    | .error _ => false) = true := by native_decide

/-! ## §F. The flagship, asserted where it now lives

    The in-place quicksort's acceptance test — `Sorted` and the permutation-count
    equation over the exit snapshot, no declared `back` anywhere in the call
    tree — is a fuel-threaded cohort written as one `fn` chain in the surface
    (`S23Direct`), checked against no table and run to a sorted list. Everything
    about it is asserted there: the headline check, the run against Lean's own
    sort on several inputs, and the twin battery of deliberately-wrong variants.

    What belongs in THIS file is the differential — the one thing that is about
    programs rather than about quicksort specifically: the two machines agree
    on the whole final state of the largest program in the corpus. -/

/-- The two machines agree on the whole final state of the flagship — the
    differential, run on a program at the largest scale the corpus has. Seeded
    since the docs/21 train: the flagship is a `Checked`, its caller a fragment,
    and the agreement is `S9Diff.diffFrom` (seed entries dropped on both sides). -/
example : Dllbc.Tests.S9Diff.diffFrom Dllbc.Tests.S23Direct.qsM
  (Dllbc.Tests.S23Direct.qsCallerTail [3, 1, 2]) = true := by native_decide

/-! ## §G. The array flagship, likewise asserted where it lives

    `quicksortA` is the array-cursor in-place scan: it carves, swaps through
    element borrows, and returns an index. It shares no code with §F's list
    quicksort — not the program, not the predicates, not the partition, not the
    container — and every claim about it (the check, the run, the twin battery,
    the cross-differential against the list sort) is asserted in `S25ArrSort`
    itself, on the same program.

    **The finding worth carrying**: the array cohort was already fuel-threaded
    from the start (its recursions decrease on an explicit fuel parameter, not
    on the borrow), so fuel-threading costs this lane nothing. Its carve
    machinery — the part of the corpus that leans hardest on the call
    boundary's re-mint of borrowed state — transferred to the sealed-program
    form without a single adjustment, which is strong evidence that a
    declaration's call-boundary opacity and a sealed λ's call rule really are
    the same mechanism reached two ways. -/

/-! ## §H. Both dispatch surfaces, for the rules this file added

    A statement-position `match` or `let` is reached through a second dispatch
    surface (the driver that walks a symbolic match's branches), not through the
    top-level expression cases directly. Every rule this file added — admitting
    globals at a runtime λ or a seal, and ending scope — has to be exercised
    where that surface sends a real body, INSIDE a branch of a symbolic match,
    and not only at the top level.

    Both rules are reached there by construction: a runtime λ and a seal are
    always expressions (a let's right-hand side, an argument, a tail), and the
    driver reaches every expression the same way it does at the top level.
    Ending scope runs per path after the walk, so a forked path gets its own.

    Each is placed inside a branch with a negative twin at the same position, so
    the branch is not merely skipped. -/

/-- A symbolic scrutinee at the top level of a program: an abstract call's result
    is a σ, and matching on one is what forks the driver's paths. The branch
    bodies are spliced `prog_parse { }` fragments (docs/22): a body names `F`
    and `m` — the program-level binding above and the arm's own binder — and
    means them where it lands, which is what used to force these to be raw
    `Term`s with `F` and `k` at hand-chosen ids. (The arm binder is `m` rather
    than the raw's `k`: a fragment's `k` is the `Id` eliminator, docs/22 §7.1.) -/
def hSplit (inZ inS : Term) : Term := prog_parse {
  let F = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let n = F(3);
  match n { Z => inZ, S(m) => inS } }

-- H0. The split is real: two paths, not one.
example : (programEnvs (hSplit .unit .unit)).length == 2 := by native_decide

-- H1. A global-referencing runtime λ, formed and called inside a branch. `F` is
-- the program-level binding two `let`s above; the branch is a body, so this
-- exercises the admitted-globals rule through the branch driver.
def hGlobal (bad : Bool) : Term :=
  hSplit .unit (prog_parse {
    let G = λ(y : Nat){ F y };
    let r = G(m);
    %(if bad then prog_parse { True } else .unit) })
example : progOk (hGlobal false) = true := by native_decide
-- The negative twin at the SAME position: the branch is entered and its result
-- audited, so the accept above is not the branch being skipped.
example : progRejects (hGlobal true) "does not have return type" = true := by native_decide

-- H2. A capture inside a branch is refused there too — the fence is not weaker
-- on a path than at the top level. (`m` is the branch's own binder, a `Nat`, so
-- this is data capture: the same rejection §D2a pins, reached the other way.)
def hCapture : Term :=
  hSplit .unit (prog_parse { let G = λ(y : Nat){ let z = m; y }; () })
example : progRejects hCapture "a runtime (lowercase) binding" = true := by native_decide

-- H3. A seal inside a branch fires its audit there, in that branch's own state.
def hSeal (bad : Bool) : Term :=
  hSplit .unit (prog_parse {
    let Sf = (λ(y : Nat){ y } : %(if bad then prog_parse { Π (y : Nat) → Bool } else prog_parse { Π (y : Nat) → Nat }));
    () })
example : progOk (hSeal false) = true := by native_decide
example : progRejects (hSeal true) "does not have return type (Bool)" = true := by native_decide

-- H4. The end-of-scope demand runs per path. The borrow is lent inside ONE
-- branch only, so the path that lends must demand it back at its own end while
-- the path that does not has nothing to demand — and the differential is what
-- says both are right, since the concrete run takes exactly one of them.
def hLend : Term := prog{
  let Push = (λ(e : Nat, v : &mut (s : List Nat ~> List Nat)){
                let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut (s : List Nat ~> List Nat)) → Unit);
  let l = Cons(1, Nil);
  let id = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let n = id(3);
  match n { Z => (), S(m) => { let r = Push(m, &m l); () } } }
example : progOk hLend = true := by native_decide
example : progDiff hLend = true := by native_decide
-- It really is two paths, and the lending one really does end its loan: no path
-- leaves `l` holding a parked loan.
example : ((programEnvs hLend).length == 2
        && (programEnvs hLend).all (fun r => match r with
             | .ok env => !((env.lookup "l").any (fun v => match v with
                 | .loanM _ => true | _ => false))
             | .error _ => false)) = true := by native_decide
-- …and the raw walk (no end-of-scope demand) leaves one, so the assertion above
-- is about the end-of-scope demand and not about the program never lending.
example : (rawEnvs hLend).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .loanM _ => true | _ => false)
    | .error _ => false) = true := by native_decide

end Dllbc.Tests.S26Prog
end

section
/-!
# What a recursion leaves behind

DLLBC is meant to be an eager language: recursing over a `Nat` should run all the
way to the end rather than leaving anything unevaluated in the result. The
subject below is one recursive function whose motive is data (a `List Nat`, not
a function type) with an empty residual telescope (the scrutinee is its only
parameter):

    fn Build [n] (n : Nat) -> List Nat {
      match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
    }

Because its base-case arm has no binders to apply a value to, it can end up
handed back as-is rather than reduced, leaving an unevaluated recursor spine
sitting inside the constructed list where the program wrote a finished value.
Nothing else in the corpus notices this, because no other recursive function
here consumes a data-motive recursion's result — every other one writes through
a borrow and returns `Unit`. The three programs below each consume the result a
different way, to pin exactly what "eager" has to mean operationally. -/

open Dllbc

namespace Dllbc.Tests.S33Eager

/-- The subject. Spelled once and spliced, so the three programs below differ in
    exactly what they do with the result. -/
def build : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  () }

/-! ## §A. Demand it with a runtime match

    The tail's match lives in its own `fn` for a reason unrelated to eagerness:
    a statement match nested directly inside another match's arm lands back in
    expression position and is refused there ("only a statement-position match
    may split"), which is a separate, pre-existing limit of the normalizer.
    Spelling the inner match as a callee keeps this test about the thing it is
    about. -/

def demandMatch : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  fn Split (l : List Nat) -> Unit {
    match l { Nil => (), Cons(h, t) => () }
  };
  let r = Build(1);
  match r {
    Nil => (),
    Cons(hd, tl) => { Split(tl); () }
  };
  () }

-- The checker accepts: to it `r`'s tail is an ordinary existential of type
-- `List Nat`, and the split is the ordinary symbolic one.
example : progOk demandMatch = true := by native_decide
-- The executing machine agrees: `Build(1)` evaluates to
-- `Cons Z (Cons (S Z) Nil)`, a finished list, so matching on its tail is an
-- ordinary match on an ordinary list rather than getting stuck on an unreduced
-- recursor spine.
example : progRuns demandMatch = true := by native_decide

-- …and the recursion really did run all the way to the end, which is what says
-- the two lines above are not the match being skipped. `Build(3)` is four
-- `Cons` cells deep, the last of them the base arm's `Cons(1, Nil)`.
def buildsToEnd : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  let r = Build(3);
  () }
example : (match runProgram buildsToEnd with
   | .ok e => (e.lookup "r").map Val.pretty
   | .error _ => none)
  = some "Cons Z (Cons Z (Cons Z (Cons (S Z) Nil)))" := by native_decide

/-! ## §B. Demand it as knowledge — the differential's own shape

    `let L = Len r` is a capital `let`, so its right-hand side is ⇝-read, and a ⇝
    read of an unreduced recursor spine is refused by name ("is state, not
    knowledge"). If the machines disagree about this SAME program with no rule
    to appeal to — one accepting it, the other unable to run it — that is
    exactly the shape a differential exists to catch, which is why fixing this
    needed a kernel change rather than a macro tidy-up. -/

def demandLen : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  let r = Build(1);
  let L = Len r;
  () }

example : progOk demandLen = true := by native_decide
-- The headline pair: neither line alone says anything, but together they say
-- the machines agree about a program that, without eager recursion, they would
-- have had no rule to reconcile.
example : progRuns demandLen = true := by native_decide

/-! ## §C. Never demand it — and overwrite it through a borrow

    An unevaluated tail that is never forced would once have made writing over
    it free, purely because there was nothing there yet to force. Under eager
    recursion the tail is a finished list from the start, so this is simply an
    ordinary overwrite of one, and the verdict is the same either way. -/

def overwriteTail : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  let r = Build(1);
  let b = &m r;
  match b {
    Nil => (),
    Cons(hd, tl) => { *tl := Nil; () }
  };
  () }

example : progOk overwriteTail = true := by native_decide
example : progRuns overwriteTail = true := by native_decide
-- …and the write really landed, which is what says the run above is not vacuous.
example : (match runProgram overwriteTail with
   | .ok e => (e.lookup "r").map Val.pretty
   | .error _ => none) = some "Cons Z Nil" := by native_decide

/-! ## §D. Per-call freshness — two results, one of them mutated

    A recursion is a function, so two calls of it are two values, and writing
    through one must not be visible in the other. This holds regardless of the
    mechanism that provides it — the pair below pins the property itself, so a
    later change to how it is provided has to keep saying so here. -/

/-- Mutate the cell the base arm built. -/
def twoBuildsBase : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  let r1 = Build(0);
  let r2 = Build(0);
  let b = &m r1;
  match b { Nil => (), Cons(hd, tl) => { *hd := 9; () } };
  () }

example : progOk twoBuildsBase = true := by native_decide
example : progRuns twoBuildsBase = true := by native_decide
example : (match runProgram twoBuildsBase with
   | .ok e => ((e.lookup "r1").map Val.pretty, (e.lookup "r2").map Val.pretty)
   | .error _ => (none, none))
  = (some "Cons (S (S (S (S (S (S (S (S (S Z))))))))) Nil", some "Cons (S Z) Nil")
  := by native_decide

/-- Mutate a cell the recursion built — the tail of `Build(1)`, which under eager
    recursion renders as a finished list rather than an unreduced recursor
    spine. -/
def twoBuildsTail : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  let r1 = Build(1);
  let r2 = Build(1);
  let b = &m r1;
  match b { Nil => (), Cons(hd, tl) => { *tl := Nil; () } };
  () }

example : progOk twoBuildsTail = true := by native_decide
example : progRuns twoBuildsTail = true := by native_decide
example : (match runProgram twoBuildsTail with
   | .ok e => ((e.lookup "r1").map Val.pretty, (e.lookup "r2").map Val.pretty)
   | .error _ => (none, none))
  = (some "Cons Z Nil", some "Cons Z (Cons (S Z) Nil)") := by native_decide

/-! ## §E. `Ih` is capital when it holds a function, and citing it twice is free

    An induction hypothesis binder is capital exactly when it holds a function
    (a Π motive, where the residual telescope carries borrows) and lowercase
    when it holds the recursive result directly (a data motive with an empty
    residual telescope, where under §A-§D the result is a finished value moved
    and returned like any other).

    The pair below is the property capitalisation has to preserve: a capital
    binder is ⇝-read, which is non-consuming, so an arm may cite `Ih` twice.
    Quicksort needs exactly this — it recurses twice from one arm. `Bump(2, …)`
    increments three times, which is the count only a doubling recursion
    reaches. -/

def citesIhTwice : Term := prog{
  fn Bump [n] (n : Nat, v : &mut Nat) -> Unit {
    match n { Z => (), S(k) => { Bump(k, &m *v); Bump(k, &m *v); *v := S(*v); () } }
  };
  let acc = 0;
  let b = &m acc;
  Bump(2, b);
  let r = acc;
  () }

example : progOk citesIhTwice = true := by native_decide
example : (match runProgram citesIhTwice with
   | .ok e => (e.lookup "r").map Val.pretty
   | .error _ => none) = some "S (S (S Z))" := by native_decide

end Dllbc.Tests.S33Eager
end

section
namespace Dllbc.Tests.S32Backstop
open Dllbc

/-! ## What is left of the mode backstop (suspensions.md §2.5)

    "A function may not land in a runtime binding" is enforced at exactly one
    site now: `refuseFnBinding`, at the `let`. Two other checks that used to
    enforce the same rule are gone — one because `fenceComptime` already
    refuses the same programs a layer earlier, the other because the site it
    guarded is unreachable. This battery is the evidence for all three. -/

-- `bindFields`' check is unreachable, not redundant: to put a function in a
-- constructor field you must ⇒-read one, and the bindings that hold one are
-- capital, which the erasure fence refuses. The field never receives a
-- function, so the check there had nothing left to catch.
def fieldFn : Term := prog_parse {
  fn Inc (n : Nat) -> Nat { S n };
  let p = Pair(Inc, 1);
  () }
example : progRejects fieldFn "cannot be ⇒-moved" = true := by native_decide

/-! ## The rule: a runtime binding may never hold a function value

    A proof of a ∀-statement is a λ, and the corpus binds those at lowercase
    names, so nothing in this calculus alone distinguishes a proof from a
    computation — both bind a partial application at a Π type, with no
    Prop/Type split to tell them apart. Σ0 resolves this positionally instead:
    every position that can hold a function now has a way to say "comptime" —
    a capital `let`, a ⇝ parameter, a Σ0 component or tail, an ascription, a
    recursor arm — so the rule becomes "a function value must arrive somewhere
    that reads by ⇝" rather than "tell a proof from a computation". Two
    refusals enforce it: `readR`'s λ arm for a λ that is written, and the pure
    lift for one that is computed.

    Each program below is kept with a one-character accepting twin, so the
    rejection is discriminating against its own accept and not against
    nothing. -/

-- `Add 1` is a function and `f` is a runtime binding; the refusal is at the
-- pure lift — the shape `readR`'s λ arm cannot see, because `Add 1` is a spine
-- until it is evaluated and a `λ (B : Nat). natRec …` after.
def computePartial : Term := prog_parse { let f = Add 1; () }
example : progRejects computePartial "⇒ produced a function value" = true := by native_decide

-- …and the accepting twin, one character away.
def computePartialCap : Term := prog_parse { let F = Add 1; () }
example : progOk computePartialCap = true := by native_decide

-- Its twin — a λ-valued runtime binding, refused by a different rule: this is
-- the refusal at `readR`'s λ arm, the destination rule, which sees the λ
-- before anything is evaluated and names every destination there is.
-- `computePartial` above is the same rule one step later, at the pure lift.
def lamValued : Term := prog_parse { let f = λ (N : Nat). Add N 1; () }
example : progRejects lamValued "needs a comptime destination" = true := by native_decide

-- …and the accepting twin, one character away: the same λ at a capital binder.
-- Without it the rejection above would also pass for a rule that refused λs.
def lamValuedCap : Term := prog_parse { let F = λ (N : Nat). Add N 1; () }
example : progOk lamValuedCap = true := by native_decide

/-! ## The Σ component's binder mode, and exactly how far it reaches

    A capital binding handed out as a Σ component used to fail, because
    `readArgs` reads a `ctorApp`'s arguments with no type in hand and
    therefore ⇒-reads all of them. `readResult` gives the tail of a body a
    type-directed read instead: a `Pair` checked against a `Σ` reads each
    component by that component's binder, so a capital Σ binder makes its
    component comptime and its value ⇝-read.

    These two programs are that rule and its negative control, and they differ
    in one character — the case of the Σ's binder. -/

open Dllbc.StdChainRaw in
/-- A proof returned as a Σ component at a **capital** binder: ⇝-read, accepted. -/
def sigmaProofCapital : Term := prog{
  fn F (n : Nat) -> Σ (H : Le n n). Nat { let H0 = LeReflRaw n; Pair(H0, n) };
  () }
example : progOk sigmaProofCapital = true := by native_decide

open Dllbc.StdChainRaw in
/-- The same program with the Σ binder lowercase: the component is ⇒-read, and
    the fence refuses the capital binding. Without this control the acceptance
    above would also pass for a rule that simply stopped fencing. -/
def sigmaProofLower : Term := prog_parse {
  fn F (n : Nat) -> Σ (h : Le n n). Nat { let H0 = LeReflRaw n; Pair(H0, n) };
  () }
example : progRejects sigmaProofLower "cannot be ⇒-moved" = true := by native_decide

open Dllbc.StdChainRaw in
/-- A Σ chain's last component has no binder, so there is nothing for
    `readResult` to read positionally: the same proof at the same capital
    binding, in the tail position instead of a bindered one, is rejected — the
    tail of a Σ chain is runtime-moded. Its accepting twin, one character
    away, is `sigmaTailProof0` in the Σ0 battery below, which gives the tail a
    way to say "comptime".

    This is where quicksort's `cnt` sits. Its ensures is
    `Σ (hi : List Nat). … → Π n. Id …`, and the trailing `Π n. Id …` is the
    ∀-proof: five components have binders and the sixth is the tail. -/
def sigmaTailProof : Term := prog_parse {
  fn F (n : Nat) -> Σ (H : Le n n). Le n n { let H0 = LeReflRaw n; Pair(H0, H0) };
  () }
example : progRejects sigmaTailProof "the TAIL of a Σ chain is runtime-moded" = true := by
  native_decide

end Dllbc.Tests.S32Backstop
end

section
namespace Dllbc.Tests.S33Sigma0

open Dllbc Dllbc.Tests

/-! ## Σ0 — the comptime tail (suspensions.md §2.7)

    `Σ0 (x : A). P` is the pair whose second projection is comptime — DLLBC's
    subset type, with comptime where Lean's `Subtype`/Coq's `sig` use
    Prop/irrelevance. It is not a new former: it is `sigmaT` with the existing
    `Term.cmpT` on the codomain, the same marker a capital binder puts on a
    domain, seen from the other end of the pair. Same `Pair`, same `sigmaRec`.

    Three things are pinned here — construction, destruction, erasure — and each
    against a spelling one character away, so every accept is discriminating. -/

/-! ## Construction: a proof in the tail

    `S32Backstop.sigmaTailProof` is this program with `Σ` where this one has
    `Σ0`, and it is rejected. The two differ in one character, and that
    character is the whole feature. -/

open Dllbc.StdChainRaw in
def sigmaTailProof0 : Term := prog{
  fn F (n : Nat) -> Σ0 (H : Le n n). Le n n { let H0 = LeReflRaw n; Pair(H0, H0) };
  () }
example : progOk sigmaTailProof0 = true := by native_decide

/-! A λ literal in a Σ0 tail is legal, and this is a property of the position
    rather than an accident: the tail is read by ⇝, so a λ there lands in a
    comptime channel and needs no other destination. The proof of a
    ∀-statement — the shape the mode backstop above could not accommodate
    positionally — is exactly this. -/
open Dllbc.StdChainRaw in
def tailLam0 : Term := prog{
  fn F (n : Nat) -> Σ0 (H : Le n n). (Π (N : Nat) → Le N N)
    { let H0 = LeReflRaw n; Pair(H0, λ (N : Nat). LeReflRaw N) };
  () }
example : progOk tailLam0 = true := by native_decide

/-! ## Destruction: the arm binder that receives a Σ0 tail must be capital

    `componentMode` needs no case of its own — it already asks `sctx` per
    field, and `reattachSigmaMode` writes the tail's entry the way it writes
    the first component's. Four programs: two type spellings (`Σ`/`Σ0`) times
    two arm spellings, and the diagonal is what is accepted. -/

/-- Σ0 producer, capital tail binder at the consumer: accepted. -/
def tail0Upper : Term := prog{
  fn Zap0 (v : &mut List Nat) -> Σ0 (k : Nat). Id (List Nat) (*v) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use0 (w : &mut List Nat) -> Unit
    { let Pair(k2, H2) = Zap0(&m *w); () };
  () }
example : progOk tail0Upper = true := by native_decide

/-- …and lowercase at the same consumer: refused, because the tail is comptime. -/
def tail0Lower : Term := prog_parse {
  fn Zap0 (v : &mut List Nat) -> Σ0 (k : Nat). Id (List Nat) (*v) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use0 (w : &mut List Nat) -> Unit
    { let Pair(k2, h2) = Zap0(&m *w); () };
  () }
example : progRejects tail0Lower "Capitalise the arm binder" = true := by native_decide

/-- The same consumer over a plain `Σ`: now lowercase is the legal spelling… -/
def tailRunLower : Term := prog{
  fn Zap (v : &mut List Nat) -> Σ (k : Nat). Id (List Nat) (*v) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(k2, h2) = Zap(&m *w); () };
  () }
example : progOk tailRunLower = true := by native_decide

/-- …and capital is refused. One character in the callee's return type decides
    which spelling of the caller's arm is legal, in both directions — which is
    what says the rule reads the type and not the shape. -/
def tailRunUpper : Term := prog_parse {
  fn Zap (v : &mut List Nat) -> Σ (k : Nat). Id (List Nat) (*v) Nil
    { *v := Nil; Pair(Z, Refl) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(k2, H2) = Zap(&m *w); () };
  () }
example : progRejects tailRunUpper "lower-case the arm binder" = true := by native_decide

/-! ## Erasure: the executing machine is untouched

    A Σ0 component is comptime knowledge — evaluated today, dropped by
    compilation, exactly as a capital Σ component already is. So the program runs,
    and the data component is what the run leaves behind. -/

open Dllbc.StdChainRaw in
def erase0 : Term := prog{
  fn F0 (n : Nat) -> Σ0 (k : Nat). Le n n { let H0 = LeReflRaw n; Pair(n, H0) };
  let Pair(a, H) = F0(S(S(Z)));
  let y = a; () }
example : progOk erase0 = true := by native_decide
example : (match runProgram erase0 with
           | .ok env => (env.lookup "y") == some (Val.nat 2)
           | .error _ => false) = true := by native_decide

/-! ## Elimination: `sigmaRec`, unchanged

    Σ0 introduces no new eliminator, and this is that promise as two programs:
    the same `elim` over the same pair, with the motive's binder type written
    `Σ` in one and `Σ0` in the other. `sigmaRec`'s second parameter is the type
    family `λ x. B`, and `⇝` is a mode marker rather than part of `B`, so a
    Σ0's family is its Σ twin's and the elimination is literally the same
    term. -/

open Dllbc.StdChainRaw in
def elimSig : Term := prog_parse {
  let P0 = Pair(Z, LeReflRaw Z);
  let K = elim P0 return (λ (p : Σ (k : Nat). Le Z Z). Nat) { Pair (k) (h) => k };
  () }
example : progOk elimSig = true := by native_decide

open Dllbc.StdChainRaw in
def elimSig0 : Term := prog_parse {
  let P0 = Pair(Z, LeReflRaw Z);
  let K = elim P0 return (λ (p : Σ0 (k : Nat). Le Z Z). Nat) { Pair (k) (H) => k };
  () }
example : progOk elimSig0 = true := by native_decide

end Dllbc.Tests.S33Sigma0
end

section
namespace Dllbc.Tests.S33Cmp
open Dllbc

/-! ## A `⇝` domain is transparent to the kernel's type walks

    A capital binder's mode marker sits on the Σ domain — `Σ (H : τ)`
    elaborates to `.sigmaT "H" (⇝τ) …`. Three of the walks that traverse a
    return type had no case for the `⇝τ` former: they end in a `| t => t`-shaped
    fallthrough, so a `⇝τ` was treated as a leaf and its subterm was skipped in
    silence.

    `markExit` is the one with teeth. The exit-snapshot transform stamps a
    borrow parameter's `*v` as `@exit(*v)` throughout the return type, and a
    comptime component's type was not reached — so that component alone read
    the entry payload while every other component read the exit. The symptom
    is a type error at a branch whose proof is correct: `splitOff`'s `Z` arm
    returns `Refl` at `Id Nil Nil` and the audit demanded `Id σ0 Nil` of it.

    This is a producer-side silent skip rather than a consumer problem — a
    match-arm binder's case being unchecked against the Σ's (S33Arms, below)
    is worth checking on its own terms, but it is not what unblocks this.

    Pinned as one program in two spellings one character apart, plus the lie that
    makes the accept discriminating. -/

def zapUnder (dom : Term) : Term := prog{
  fn Zap (v : &mut List Nat) -> dom { *v := Nil; Pair(Refl, unit) };
  () }

def zapV : Term := .var "v"

-- The comptime component: its `Id` mentions `*v`, so it is exactly the type
-- `markExit` has to reach through the `⇝` to stamp.
def zapCmp : Term := prog_parse { Σ (H : Id (List Nat) (*zapV) Nil). Unit }
-- …and its one-character twin, the control that says the `⇝` is the whole
-- difference.
def zapRun : Term := prog_parse { Σ (h : Id (List Nat) (*zapV) Nil). Unit }
-- …and the lie, so neither accept is vacuous: the exit is `Nil`, not `[Z]`.
def zapLie : Term := prog_parse { Σ (H : Id (List Nat) (*zapV) (Cons Z Nil)). Unit }

example : progOk (zapUnder zapCmp) = true := by native_decide
example : progOk (zapUnder zapRun) = true := by native_decide
example : progRejects (zapUnder zapLie) "does not have return type" = true := by native_decide

end Dllbc.Tests.S33Cmp
end

section
namespace Dllbc.Tests.S33Arms
open Dllbc

/-! ## The mode convention reaches the match arm

    A match arm's binders are binders, and they were the last position whose
    spelling nothing read. Both directions are checked, because they are two
    different mistakes — a capital binder over data claims erasure of something
    the match moves; a lowercase binder over a comptime component is the
    runtime-binding-holds-knowledge state the `let` already refuses
    (`fenceComptime`), reached by a rule that was not looking.

    Each direction is one program in two spellings one character apart, so each
    reject is discriminating against its own accept rather than against nothing. -/

/-! ## Direction 1 — a capital arm binder over a runtime data component

    `Cons`' head and tail are data at every type there is, which is why this
    direction needs no type in hand at all: the fixed constructor basis decides
    it, and `Pair` is the only member it does not decide. -/

def armDataLower : Term := prog{
  match Cons(Z, Nil) { Nil => (), Cons(h, t) => () } }

def armDataUpper : Term := prog_parse {
  match Cons(Z, Nil) { Nil => (), Cons(H, t) => () } }

example : progOk armDataLower = true := by native_decide
example : progRejects armDataUpper "lower-case the arm binder" = true := by native_decide

/-! ## Direction 2 — a lowercase arm binder over a comptime component

    The producer is `S33Cmp.zapCmp`'s shape: a Σ whose component binder is
    capital, so `readResult` ⇝-reads that component and the caller's
    `buildResult` mints its σ at a `⇝` type. That `sctx` entry is the whole of
    the mode source — no type is re-derived at the match. -/

def armCmpUpper : Term := prog{
  fn Zap (v : &mut List Nat) -> Σ (H : Id (List Nat) (*v) Nil). Unit
    { *v := Nil; Pair(Refl, unit) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(H2, u) = Zap(&m *w); () };
  () }

def armCmpLower : Term := prog_parse {
  fn Zap (v : &mut List Nat) -> Σ (H : Id (List Nat) (*v) Nil). Unit
    { *v := Nil; Pair(Refl, unit) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(h2, u) = Zap(&m *w); () };
  () }

example : progOk armCmpUpper = true := by native_decide
example : progRejects armCmpLower "Capitalise the arm binder" = true := by native_decide

/-! ## …and the same consumer over a runtime component is unchanged

    The control that says direction 2 keys on the producing Σ binder's case and
    not on the component sitting in a `Pair`: one character in the callee's
    return type flips which spelling of the caller's arm is legal. -/

def armRunLower : Term := prog{
  fn Zap (v : &mut List Nat) -> Σ (h : Id (List Nat) (*v) Nil). Unit
    { *v := Nil; Pair(Refl, unit) };
  fn Use (w : &mut List Nat) -> Unit
    { let Pair(h2, u) = Zap(&m *w); () };
  () }

example : progOk armRunLower = true := by native_decide

end Dllbc.Tests.S33Arms
end

section
namespace Dllbc.Tests.S32Binders
open Dllbc

/-! # Comptime-binder capitalisation, measured across the corpus

    Convention: a capital binder name is comptime, a lowercase one is runtime.
    Today the same fact is also readable from `Var.bindsSlot` — whether the
    binder has an Ω store slot id at all (`noSlot` is the sentinel) — which is
    the check the ids exist for. The functions below count, for a given term,
    how many binders follow or violate the naming convention, how many disagree
    with the slot-based reading, and several related conventions (whether a Σ
    component or match-arm binder is marked comptime). Each is run against the
    flagship program and a few hand-written library terms to confirm the corpus
    is fully migrated. -/

/-- Comptime binders (no slot) whose name is neither capitalised nor reserved —
    binders that violate the naming convention. -/
partial def lowerComptime : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && !isUpperInit x.name && !isReservedName x.name then 1 else 0)
      + lowerComptime d + lowerComptime b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => lowerComptime d + lowerComptime b
  | .app f a | .seq f a | .seal _ f a => lowerComptime f + lowerComptime a
  | .letIn _ r => lowerComptime r
  | .assign p e => lowerComptime p + lowerComptime e
  | .idT a b c => lowerComptime a + lowerComptime b + lowerComptime c
  | .ctorApp _ as | .call _ as => (as.map lowerComptime).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => lowerComptime br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => lowerComptime t
  | _ => 0

/-- Binders that DO bind a slot — these already carry their mode in their case,
    for comparison against `lowerComptime`'s count. -/
partial def slotBinders : Term → Nat
  | .lam x d b => (if x.bindsSlot then 1 else 0) + slotBinders d + slotBinders b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => slotBinders d + slotBinders b
  | .app f a | .seq f a | .seal _ f a => slotBinders f + slotBinders a
  | .letIn _ r => slotBinders r
  | .assign p e => slotBinders p + slotBinders e
  | .idT a b c => slotBinders a + slotBinders b + slotBinders c
  | .ctorApp _ as | .call _ as => (as.map slotBinders).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => slotBinders br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => slotBinders t
  | _ => 0

/-- `lowerComptime`'s twin: a comptime binder is two halves written together —
    the capital name and the `⇝` marking its domain — and `Term.clam`/`Term.cpi`
    exist so a hand-written term cannot spell one without the other.
    `lowerComptime` counts binders with the domain half but not the name half;
    this counts the reverse. The two are not symmetric in the tree: the
    hand-written kernel library is 0 because `clam` always writes both halves,
    while every surface `elim` arm binder shows up here because `elabUElim`
    builds arm binders with a bare `Term.lam` and never calls `binderDom`. Same
    scope restriction as `lowerComptime` (`!bindsSlot`). -/
partial def unmarkedCaps : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && isUpperInit x.name && !d.domComptime then 1 else 0)
      + unmarkedCaps d + unmarkedCaps b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => unmarkedCaps d + unmarkedCaps b
  | .app f a | .seq f a | .seal _ f a => unmarkedCaps f + unmarkedCaps a
  | .letIn _ r => unmarkedCaps r
  | .assign p e => unmarkedCaps p + unmarkedCaps e
  | .idT a b c => unmarkedCaps a + unmarkedCaps b + unmarkedCaps c
  | .ctorApp _ as | .call _ as => (as.map unmarkedCaps).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => unmarkedCaps br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => unmarkedCaps t
  | _ => 0

/-- The direction that must be zero: a runtime binder with nowhere to put its
    argument. Lowercase says the argument arrives by ⇒ — moved or loan-seeded
    into the store — so a lowercase binder that binds no Ω slot is a binder whose
    argument has no destination. -/
partial def keyDisagree : Term → Nat
  | .lam x d b =>
    (if !x.bindsSlot && !(isUpperInit x.name || isReservedName x.name) then 1 else 0)
      + keyDisagree d + keyDisagree b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => keyDisagree d + keyDisagree b
  | .app f a | .seq f a | .seal _ f a => keyDisagree f + keyDisagree a
  | .letIn _ r => keyDisagree r
  | .assign p e => keyDisagree p + keyDisagree e
  | .idT a b c => keyDisagree a + keyDisagree b + keyDisagree c
  | .ctorApp _ as | .call _ as => (as.map keyDisagree).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => keyDisagree br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => keyDisagree t
  | _ => 0

/-- The other direction, which is not zero: a capital binder that binds an Ω
    slot. Legitimate, because `seedTelescopeV` slots every parameter regardless
    of case, and capital says how the argument is read, not where it lands. -/
partial def comptimeSlotParams : Term → Nat
  | .lam x d b =>
    (if x.bindsSlot && (isUpperInit x.name || isReservedName x.name) then 1 else 0)
      + comptimeSlotParams d + comptimeSlotParams b
  | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => comptimeSlotParams d + comptimeSlotParams b
  | .app f a | .seq f a | .seal _ f a => comptimeSlotParams f + comptimeSlotParams a
  | .letIn _ r => comptimeSlotParams r
  | .assign p e => comptimeSlotParams p + comptimeSlotParams e
  | .idT a b c => comptimeSlotParams a + comptimeSlotParams b + comptimeSlotParams c
  | .ctorApp _ as | .call _ as => (as.map comptimeSlotParams).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => comptimeSlotParams br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => comptimeSlotParams t
  | _ => 0

/-- λ nodes this term classifies as imperative. The number the telescope rule
    protects: if the slot test were swapped for a case test, every `fn` whose
    parameters are all capital would leave this count and lose its audit.

    Classified UNDER the pure binders each node sits below (docs/22 §3 item 8),
    exactly as `reflectC` classifies: with one `var`, a nested pure λ that
    applies an OUTER pure binder (`λ F. λ B. … F b …`) is a pure spine only
    when the outer binder is in view, and the node alone cannot see it. -/
partial def impLamsIn (pure : List String) : Term → Nat
  | .lam x d b =>
    (if Term.lamImperativeIn pure (.lam x d b) then 1 else 0) + impLamsIn pure d
      + impLamsIn (if x.bindsSlot then pure.filter (· != x.name) else x.name :: pure) b
  | .pi x d b | .sigmaT x d b | .borrowT x d b => impLamsIn pure d + impLamsIn (x :: pure) b
  | .app f a | .seq f a | .seal _ f a => impLamsIn pure f + impLamsIn pure a
  | .letIn _ r => impLamsIn pure r
  | .assign p e => impLamsIn pure p + impLamsIn pure e
  | .idT a b c => impLamsIn pure a + impLamsIn pure b + impLamsIn pure c
  | .ctorApp _ as | .call _ as => (as.map (impLamsIn pure)).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => impLamsIn pure br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => impLamsIn pure t
  | _ => 0

def impLams (t : Term) : Nat := impLamsIn [] t

-- The in-place quicksort, the largest program in the corpus, with its specs and
-- library lemmas elaborated in: every comptime binder spells its mode, and the
-- 22 runtime binders are untouched by the naming convention. The subject is the
-- honest module's persisted term, markers stripped — the census counts the
-- PROGRAM, not the twin scaffolding.
def qsFlagshipT : Term := Term.stripMarkers Dllbc.Tests.S23Direct.qsM.term
example : lowerComptime qsFlagshipT = 0 := by native_decide
example : slotBinders qsFlagshipT = 22 := by native_decide

-- Two kernel library terms, hand-written rather than elaborated: `len` and the
-- `Le` predicate the carve rule's premises are stated against.
example : lowerComptime Std.lenFnT = 0 := by native_decide
example : lowerComptime Pure.kLeFn = 0 := by native_decide

/-! **`unmarkedCaps` on the flagship and the hand-written library, both 0.**

    A recursor arm built by `elabUElim` used a bare `Term.lam` for its binders
    and never called `binderDom`, so `elim n return … { Z => …, S (A') R => … }`
    produced `λ A'. λ R. …` with plain domains where `Term.clam "A'"`/`"R"` would
    write `⇝Nat`. Every capital binder the surface elaborator wrote was affected;
    every capital binder a human wrote using `clam` was already correct. Routing
    `elabUElim`'s arm binders (and the Σ-elimination type family) through
    `binderDom` fixes it, with zero verdict changes anywhere in the corpus —
    conversion is mode-blind by construction (`Term.convEq`), so the marker
    was inert to every judgment that runs. It is not inert to `Term.alphaEq`,
    the key binder abstraction generalizes with, which is why the asymmetry
    was worth removing rather than documenting. -/
example : unmarkedCaps qsFlagshipT = 0 := by native_decide
example : unmarkedCaps Dllbc.Tests.S24Arrays.sort2.term = 0 := by native_decide
example : unmarkedCaps Std.lenFnT = 0 := by native_decide
example : unmarkedCaps Pure.kLeFn = 0 := by native_decide
example : unmarkedCaps Pure.kAddFn = 0 := by native_decide

/-! ### Why `bindsSlot`, not the case test, decides slotting

    Swapping `Var.bindsSlot` for a capitalisation-based case test would cost
    exactly 4 binders in the flagship — all a capital telescope parameter
    binding an Ω slot, because `seedTelescopeV` slots every parameter, comptime
    or not. The swap should not happen: case and `bindsSlot` answer different
    questions. **Case** is the read mode — ⇝ or ⇒, erased or moved. **`bindsSlot`**
    is the location — whether the argument lands in Ω; the telescope rule says a
    telescope binder binds a slot regardless of case.

    So the two checks below are not the same claim measured twice: `keyDisagree`
    (lowercase, no slot) is a real invariant that must be zero — a runtime
    binder whose argument has nowhere to land — while `comptimeSlotParams`
    (capital, slotted) is the telescope rule's own population, which is content,
    not debt. -/
example : keyDisagree qsFlagshipT = 0 := by native_decide
example : keyDisagree Std.lenFnT = 0 := by native_decide
example : keyDisagree Pure.kLeFn = 0 := by native_decide

-- The telescope rule's population: each `Hf`/`Hfuel` is a proof parameter of a
-- recursive `fn` (`Partition`, `AppendBack`, `Quicksort`) carried capital because
-- the length/fuel facts it relates are themselves capital; each `Ih` is the
-- recursor's self-view of the function at the predecessor, which is a Π and so
-- must be comptime under §2.5 (no runtime binding may hold a function).
example : comptimeSlotParams qsFlagshipT = 9 := by native_decide

/-! **The count the rule protects.** A case test at `Term.lamImperative` would
    take every all-capital-parameter `fn` out of this number. It lands on
    `slotBinders`' own 22, and that is arithmetic rather than
    coincidence: a telescope is nested λs, so a λ node is imperative exactly when
    a slot binder sits at or below it in its own chain, and each slot binder is
    the innermost such node for exactly one prefix. -/
example : impLams qsFlagshipT = 22 := by native_decide


/-! ## The Σ half: comptime components and the arm binders that consume them

    `lowerComptime` above counts λ binders and is blind to Σ's — `.sigmaT` is on
    the line that recurses without inspecting the binder. These functions cover
    that position, on both sides of it: which Σ components are marked comptime,
    and which match-arm binders consuming them are correspondingly capitalised. -/

/-- Σ binders that declare their component comptime (`⇝` on the domain) — the
    producer side. -/
partial def cmpSigmas : Term → Nat
  | .sigmaT _ d b => (if Term.domComptime d then 1 else 0) + cmpSigmas d + cmpSigmas b
  | .lam _ d b | .pi _ d b | .borrowT _ d b => cmpSigmas d + cmpSigmas b
  | .app f a | .seq f a | .seal _ f a => cmpSigmas f + cmpSigmas a
  | .letIn _ r => cmpSigmas r
  | .assign p e => cmpSigmas p + cmpSigmas e
  | .idT a b c => cmpSigmas a + cmpSigmas b + cmpSigmas c
  | .ctorApp _ as | .call _ as => (as.map cmpSigmas).foldl (· + ·) 0
  | .matchE _ _ bs => (bs.map (fun br => cmpSigmas br.body)).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => cmpSigmas t
  | _ => 0

/-- Match-arm binders spelled capital — the consumer side, and the population
    `checkArmModes` refuses to leave lowercase. -/
partial def capArms : Term → Nat
  | .matchE _ _ bs =>
    (bs.map (fun br =>
      (br.binders.filter (fun x => isUpperInit x.name)).length + capArms br.body)).foldl (· + ·) 0
  | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => capArms d + capArms b
  | .app f a | .seq f a | .seal _ f a => capArms f + capArms a
  | .letIn _ r => capArms r
  | .assign p e => capArms p + capArms e
  | .idT a b c => capArms a + capArms b + capArms c
  | .ctorApp _ as | .call _ as => (as.map capArms).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => capArms t
  | _ => 0

/-- The ones that stay lowercase, the other half of the claim: the check is
    bidirectional, so this number is asserted by the same run. -/
partial def lowerArms : Term → Nat
  | .matchE _ _ bs =>
    (bs.map (fun br =>
      (br.binders.filter (fun x => !isUpperInit x.name)).length + lowerArms br.body)).foldl (· + ·) 0
  | .lam _ d b | .pi _ d b | .sigmaT _ d b | .borrowT _ d b => lowerArms d + lowerArms b
  | .app f a | .seq f a | .seal _ f a => lowerArms f + lowerArms a
  | .letIn _ r => lowerArms r
  | .assign p e => lowerArms p + lowerArms e
  | .idT a b c => lowerArms a + lowerArms b + lowerArms c
  | .ctorApp _ as | .call _ as => (as.map lowerArms).foldl (· + ·) 0
  | .borrow t | .deref t | .cmpT t => lowerArms t
  | _ => 0

example : cmpSigmas qsFlagshipT = 91 := by native_decide
example : capArms qsFlagshipT = 14 := by native_decide
example : lowerArms qsFlagshipT = 22 := by native_decide

/-! **The three numbers, read together.**

      * **91 comptime Σ components.** Most are the library's — `Ub`, `Lb` and
        `Sorted` unfold to Σ chains with capital binders — plus five written by
        hand in the spec (`Hub`, `Hlb`, `Hl1`, `Hl2`, `Hs`).
      * **14 capital arm binders**, consuming those five spec components:
        `Partition`'s four in each of its two consumer chains, plus
        `Quicksort`'s `Hs1`/`Hs2`, plus the tails (`Hcnt` twice, `Hpc`,
        `Hc1`/`Hc2`) whose `sctx` entry carries `⇝` and so cannot stay lowercase.
      * **22 lowercase arm binders** — the data components (`hi`, `x`, `rest`,
        `lo`) that the same rule positively requires to stay lowercase. The
        check runs in both directions: without it, all 36 binders could be
        capital. -/

end Dllbc.Tests.S32Binders
end
