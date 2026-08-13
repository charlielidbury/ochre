import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.ProgMacro
import Dllbc.Tests.Functions
import Dllbc.Tests.Boundaries
import Dllbc.FnMacro
import Dllbc.Tests.Arrays
import Dllbc.Tests.Direct
import Dllbc.Tests.Diff
import Dllbc.Tests.ArraySort

/-!
# Programs — modes, the mixed-return containment, fuel-threading, and §8's programs-are-terms

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S26Modes.lean`
  * `S27Mixed.lean`
  * `S26Fuel.lean`
  * `S26Prog.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S26Modes.lean` ──────────────────────────────────────────────
section
/-!
# §26 (M26-B) — binder modes: capital is comptime, and the fence

Phase B of the `fn`/λ unification (`docs/combining-fns.md` §6). One convention
enters the language — **a capitalized binder is comptime, a lowercase one is
runtime** — and it is carried by two mechanisms that are the two halves of the
same sentence:

  * **The comptime-argument rule.** At a ⇒-call, an argument standing in a
    capital-bindered position is evaluated under ⇝: a pure, NON-CONSUMING read.
    The binder is erased — never moved, citable after any call.
  * **The fence.** A capital binder is usable only in ⇝-positions (types,
    proofs, capital arguments of other calls). A ⇒-move of it, a runtime match
    on it, a borrow of it, a write through it, an index of it, and a ⇒-call of
    it are each rejected.

**Where the mode lives.** Two places, because there are two kinds of binder and
they record their identity differently. A *runtime* binder is a `Var` — an id
and a name — so its mode is its name's case (`Var.isComptime`); this covers
telescope parameters, `let`, and match binders, and needs no representation
change at all. A *pure* binder carries a source name (M30 step 2) but not its
mode — the two namespaces are separate — so its mode rides
on the domain: `Π (X : τ) → …` is `.pi (.cmpT τ) …`. `Term.cmpT` is
the sibling of `borrowT` — three modes at one syntactic place, the two
non-default ones marked.

**Case is inert under ⇝, mechanically.** `Val.beq` unwraps `cmpT` on either
side, so `convert` — and every comptime judgment above it — cannot observe a
mode. §E pins this from both sides: the two Π's convert, and the same two Π's
give different call behaviour. Modes route ⇒'s arguments and fence its bodies;
⇝ is the room the distinction was never meant to reach.

**Negative controls are per DEMAND SITE** (phase A's finding, now doctrine).
`readC` computes without checking, so a rule branch nobody demands is a rule
branch nobody tested. §B enumerates the demand sites and gives each its own
control, each paired with the lowercase twin that is ACCEPTED — which is a
stronger liveness check than flipping the assertion, because it shows the
rejection is about the mode and not about the program.
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl LeTrans)
-- `diffC` moved to `S9Diff` when M26-C merged the two simulation relations into
-- one (segments AND computation); same name, same property, one definition.
open Dllbc.Tests.S9Diff (diffC)

namespace Dllbc.Tests.S26Modes

/-! ## §A. The comptime-argument rule — R16's proof consumption, at its source

    "Passing a proof to a call moves it" (R16) forced the capture-before-call
    staging that `S25ArrSort`'s `mkTop`/`mkHf` and M23's four builders exist to
    perform. The diagnosis in §6 is that the pain was never "proofs are linear";
    it is that a call site had only one arrow. A capital parameter gives it the
    other one.

    The subject must be a TELESCOPE proof, not a `let`-bound proof term: a proof
    *spine* is already index-kind and already copies on read (§2.1), so it would
    show nothing. A telescope proof is a σ whose type is a stuck `natRec` spine —
    not `Nat`/`Bool`/`Id`/`Type`/`Π` — so `indexKindV` says MOVE, and that is
    exactly the class R16 is about. -/

-- `useLe` and its capital twin `useLeC` are the callees of every pair below, one
-- character apart. Each cohort is written as ONE chain — callee above caller —
-- because a `%`-spliced tail could not itself declare functions until M32 R4
-- (both chains numbered their slots from `progBase` and collided by id). It can
-- now; the callee line stays repeated because that is what was written.

-- A1. THE PAIN. The proof is passed, and citing it afterwards is a use-after-move.
def a1 : Term := prog{
  fn UseLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { UseLe(n, m, hnm); hnm };
  () }
example : progRejects a1 "holds ⊥" = true := by native_decide

-- A2. THE FIX. The same program against the capital twin: accepted, because the
-- argument was ⇝-read and never left the caller's slot.
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

-- A4. The staging that R16 forced, and what it becomes. `mkHf`'s shape — capture
-- a proof into a λ *before* the call that consumes it — still works, and is now
-- unnecessary: A3 is the same program without it.
def a4 : Term := prog{
  fn UseLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let Hnm = hnm;                          -- §2.4: the snapshot, named
    let Mk = λ (u : Unit). Hnm; UseLe(n, m, hnm); Mk unit };
  () }
example : progOk a4 = true := by native_decide

/-! ### A5. `match fuel` against its capital twin

    The flagship's two halves, isolated: a lowercase binder is branched on, and
    the capital twin — same type, same position — cannot be. This is the pair
    that says the modes are doing work rather than decorating. -/

def a5lo : Term := prog{ fn A5lo (fuel : Nat) -> Unit { match fuel { Z => (), S(f2) => () } }; () }
def a5hi : Term := prog{ fn A5hi (Fuel : Nat) -> Unit { match Fuel { Z => (), S(f2) => () } }; () }
example : progOk a5lo = true := by native_decide
example : progRejects a5hi "cannot be the scrutinee of a runtime match" = true := by native_decide

-- A6. A comptime argument must be a COMPTIME term. A call's result is a fresh
-- existential with no ⇝ reading, so it cannot be spliced into a capital position
-- directly — it must be `let`-bound first. An honest rejection rather than a
-- silent fall-back to ⇒, and the `let`-bound form immediately above works.
def a6bad : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn GiveLe (a : Nat) -> Le a a { %LeRefl a };
  fn Caller (n : Nat) -> Unit { UseLeC(n, n, GiveLe(n)); () };
  () }
def a6ok : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn GiveLe (a : Nat) -> Le a a { %LeRefl a };
  fn Caller (n : Nat) -> Unit
  { let p = GiveLe(n); UseLeC(n, n, p); UseLeC(n, n, p); () };
  () }
example : progRejects a6bad "not in the comptime fragment" = true := by
  native_decide
example : progOk a6ok = true := by native_decide

/-! ## §B. The fence — one control per DEMAND SITE, each with its lowercase twin

    Phase A's finding generalized: `readC` computes without checking, so a rule
    branch nobody demands is a rule branch nobody tested. The sites below are the
    ⇒-rules that would make an erased binder observable, and each is paired with
    the *same program over a lowercase binder*, which is accepted. That pairing
    is the liveness check: it shows the rejection is about the MODE and not about
    the program being ill-formed some other way. -/

-- B1. The ⇒-move.
def b1hi : Term := prog{ fn B1 (N : Nat) -> Unit { let y = N; () }; () }
def b1lo : Term := prog{ fn B1 (n : Nat) -> Unit { let y = n; () }; () }
example : progRejects b1hi "cannot be ⇒-moved" = true := by native_decide
example : progOk b1lo = true := by native_decide

-- B2. The runtime match — §A5 above, which is where it earns its keep.

-- B3. The borrow.
def b3hi : Term := prog{ fn B3 (N : List Nat) -> Unit { let b = &m N; () }; () }
def b3lo : Term := prog{ fn B3 (n : List Nat) -> Unit { let b = &m n; () }; () }
example : progRejects b3hi "cannot be borrowed" = true := by native_decide
example : progOk b3lo = true := by native_decide

-- B4. The write-through (⇐).
def b4hi : Term := prog{ fn B4 (N : Nat) -> Unit { N := 3; () }; () }
def b4lo : Term := prog{ fn B4 (n : Nat) -> Unit { n := 3; () }; () }
example : progRejects b4hi "cannot be written through" = true := by native_decide
example : progOk b4lo = true := by native_decide

-- B5. The index/slice step. Built by hand rather than through the surface: the
-- fence fires on the place's *syntactic root* before `placeToPos` navigates
-- anything, which is the property being pinned (a place expression may carve,
-- and a fence that ran after that would have already reorganized Ω).
def b5body : Term := .letIn ⟨1, "e"⟩ (.index (.var ⟨0, "N"⟩) (.ctorApp "Z" []) none) .unit
-- The body is spliced with `%`, which is how a hand-built `Term` reaches a `fn`
-- statement: the statement's body is a block and `%t` is a block's final
-- expression, so the escape hatch `decl{ … = %t }` provided is the ordinary
-- splice here.
def b5hi : Term := prog{ fn B5 (N : Nat) -> Unit { %b5body }; () }
example : progRejects b5hi "cannot be indexed or sliced" = true := by native_decide

-- B6. A capital binder handed to a LOWERCASE parameter. Same rejection as B1
-- and a different demand site — `processArgs` reads a runtime parameter's
-- argument with ⇒, so the fence fires there. This is the direction that makes
-- the fence coherent: a comptime binder cannot launder itself into runtime by
-- being passed to something that wants a runtime value.
def b6 : Term := prog{
  fn UseLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, Hnm : Le n m) -> Unit
  { UseLe(n, m, Hnm); () };
  () }
example : progRejects b6 "cannot be ⇒-moved" = true := by native_decide

/-! ### B7. §6.3's distinction, DISSOLVED (M31 Stage A)

    This used to be the one place where kind could not decide the mode. A capital
    function-typed binder was a SPEC parameter — citable in a type, where ⇝ gives
    the structured neutral, and refused as a callee by `.callV`'s fence — while
    `map_apply (g : …)` was the lowercase twin that calling was the whole point
    of. Two parameters, one function, and a caller had to know which door it came
    in by.

    M31 §2.2 deletes the fence, and with it the split: **a call's head is fetched
    by ⇝**, which is what a capital binder is read by anyway, so a capital
    function-typed parameter is both citable and callable and there is no second
    kind of parameter left to be. The twins collapse — these two tests are now the
    same test in two cases, kept as a pair only to assert that neither case is the
    privileged one. -/

def b7spec : Term := prog{
  fn B7spec (G : Π (x : Nat) → Nat, n : Nat) -> Unit { let r = G(n); () };
  () }
example : progOk b7spec = true := by native_decide
example : progOk S26Seal.apply1 = true := by native_decide

-- …and the citation that IS allowed: `G a` in a type position, where the whole
-- content is §2.1's structured neutral. `G` is never supplied at runtime.
def b7cite : Term := prog{
  fn B7cite (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk b7cite = true := by native_decide

/-! ### B7b. Function bindings are comptime-moded (M31 Stage A, §2.1/§2.2)

    The three assertions Stage A's semantic core is worth, stated where B7's
    dissolution leaves off. A `fn` name may be CAPITAL and everything about it
    still works — it is declared, it is called, and the executing machine runs it
    — which is the whole of "a function binding flips mode".

    `let F = Main` is the one the playground failed at, and it failed at two
    independent layers: the surface had no reading for a bare `fn` name at all
    (only `f(…)` resolved, through `retarget`), and the kernel refused reading a
    function out of its slot. Stage A answers the first — a `fn` name is an
    ordinary binding, so a bare name denotes it — and the second never fires,
    because a capital binding reads its right-hand side by ⇝ and the function-read
    refusal is a ⇒ rule. Both halves, one test. -/

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

-- E7's confirmation, as a run rather than as a claim: a comptime-moded slot is
-- read by the executing machine the way it always read `rfn` — a plain slot read,
-- no detour through the normalizer — so `Bump` is still holding its runtime λ at
-- the end and `y` is the value the call computed.
def b7run : Term := prog{
  fn Bump (n : Nat) -> Nat { Add n 1 };
  let y = Bump(1);
  () }
example : progRuns b7run = true := by native_decide

/-! ### B8/B9. Borrow-typed binders must be lowercase — checked, not assumed

    §6 states this as a requirement on the design; it is checked at BOTH ends,
    and the two rejections are distinguishable so the site is pinned rather than
    inferred. The declaration is caught by `seedTelescope` (the honest place: the
    signature is wrong); the call site is caught by `processArgs`, which matters
    for a table entry that was never itself checked. -/

def b8 : Term := prog{ fn B8 (V : &mut List Nat) -> Unit { () }; () }
example : progRejects b8 "telescope: parameter 'V' is capitalized" = true := by native_decide

def b9 : Term := prog{
  fn B8 (V : &mut List Nat) -> Unit { () };
  fn Caller () -> Unit { let x = Cons(1, Nil); B8(&m x); () };
  () }
-- The needle is NAME-FREE since M27-δ, and the reason belongs beside it: `fsig`
-- stores the ascribed Π itself now, and a Π has no binder names — `piBinderNames`
-- synthesizes `A0`/`a0` at the call, encoding the MODE (which is what the rule
-- needs) and losing the display name (which is what the message had). A
-- synthesized name is as unstable as a σ id, so pinning one would rot.
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

    §6 pays for "capital is the mode marker" with one rule: the constructor names
    are keywords. Checked at elaboration — these are `Macro` errors, so they are
    exhibited rather than asserted (a rejected macro does not produce a `FnDef` to
    test). What CAN be asserted is the other half: the surface no longer decides
    `F(x)` by CASE. `f(…)` is a constructor application exactly when `f` is in
    the fixed basis, which is what makes `G(n)` above a call rather than a
    silently-mistyped `ctorApp "G"`. B7 is that assertion. -/

example : Surface.reservedBinder "Cons" = true := by native_decide
example : Surface.reservedBinder "Nat" = true := by native_decide
-- Lowercase names are NOT reserved: they were always shadowable, shadowing them
-- is ordinary scoping, and reserving `j`/`k` would cost every program its loop
-- indices for no disambiguation at all (`insert_at`'s own `k` parameter).
example : Surface.reservedBinder "k" = false := by native_decide
example : Surface.reservedBinder "unit" = false := by native_decide
example : Surface.reservedBinder "Hfuel" = false := by native_decide

/-! ## §C. Capital `let` — the comptime binding, and what it actually buys

    `let X = e` evaluates `e` under ⇝, erases `X`, consumes nothing, and confines
    `X` to ⇝-positions. For a proof *spine* right-hand side this changes nothing
    observable (a spine already goes through the pure lift, which is `readC`), so
    the payoff has to be looked for where ⇒ and ⇝ genuinely differ — and there is
    one such place, which is the one the staging pain lives in.

    **`*v` is a TAKE under ⇒ and a PROJECTION under ⇝.** `let l = *v` moves the
    payload out and leaves a hole; `let L = *v` reads the snapshot and leaves the
    borrow intact. That is `S25ArrSort`'s `mkTop` — "capturing `*a` while it
    still IS the entry value is the dodge" — available as a binding instead of as
    a λ built before the call. -/

def c1 : Term := prog{
  fn C1 (v : &mut List Nat) -> Id (List Nat) (*v) (old *v) { let L = *v; Refl };
  () }
def c1bad : Term := prog{
  fn C1bad (v : &mut List Nat) -> Id (List Nat) (*v) (old *v) { let l = *v; Refl };
  () }
example : progOk c1 = true := by native_decide
-- The runtime take leaves a hole in the borrow, and a hole satisfies no type
-- (§5.4). Same program, one character — and the rejection names the hole, so
-- this is the take-vs-projection difference and not some other breakage.
example : progRejects c1bad "holds a hole (⊥) at return" = true := by native_decide

-- C2. The fence applies to a capital `let` exactly as to a capital parameter —
-- so the snapshot above is a SPECIFICATION binding, not a free copy of the data.
def c2 : Term := prog{ fn C2 (v : &mut List Nat) -> Unit { let L = *v; let y = L; () }; () }
example : progRejects c2 "cannot be ⇒-moved" = true := by native_decide

-- C3. The right-hand side must have a ⇝ reading. A call's result is a fresh
-- existential and has none, so a capital `let` cannot bind one — honest, and
-- pointing at the lowercase `let` that can.
def c3bad : Term := prog{
  fn GiveLe (a : Nat) -> Le a a { %LeRefl a };
  fn Caller (n : Nat) -> Unit { let P = GiveLe(n); () };
  () }
example : progRejects c3bad "not in the comptime fragment" = true := by native_decide

-- C4. Locally-derived certificates without staging: a capital `let` builds the
-- certificate, and citing it at capital argument positions never consumes it.
def c4 : Term := prog{
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let Q = LeTrans n m m hnm (%LeRefl m);
    UseLeC(n, m, Q); UseLeC(n, m, Q); hnm };
  () }
example : progOk c4 = true := by native_decide

/-! ## §D. Erased data — the capability kind-derivation cannot express

    A capital `N : Nat` used only in types is QTT's quantity 0. The point is
    sharp precisely because `Nat` is already index-kind: §2.1's copy-on-read
    heuristic classifies it as copyable, and copy-on-read is *not* erasure — a
    copyable binder can still be branched on. The mode is what forbids that, and
    kind cannot derive it, because the two binders below have the same kind. -/

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
def d3 : Term := prog{ fn D3 (N : Nat) -> Unit { match N { Z => (), S(k) => () } }; () }
example : progRejects d3 "cannot be the scrutinee of a runtime match" = true := by native_decide

/-! ## §E. Case is inert under ⇝ — pinned from both sides

    §6's heading, as two assertions that together say the modes are exactly as
    strong as intended and no stronger: the two Π's are the same type to every
    comptime judgment, and ⇒ still tells them apart. -/

-- E1. The mode is invisible to conversion…
example : Pure.convert 1000 (.pi "X" (.cmpT (.const "Nat")) (.const "Nat"))
                           (.pi "x" (.const "Nat") (.const "Nat")) = true := by native_decide
-- …and NOT erased by normalization, which is what leaves ⇒ something to read.
-- (`==` is mode-blind, so this has to be asked structurally.)
example : (match Pure.nf 1000 (Term.pi "X" (.cmpT (.const "Nat")) (.const "Nat")) with
           | .pi _ d _ => Term.domComptime d
           | _ => false) = true := by native_decide

-- E2. `Add` stays all-lowercase and is cited in a spec regardless — you never
-- capitalize a definition to use it in a type. Both cases of the CITING
-- function's own binders work, because the citation happens under ⇝.
def e2lo : Term := prog{ fn E2lo (a : Nat, b : Nat) -> Id Nat (Add a b) (Add a b) { Refl }; () }
def e2hi : Term := prog{ fn E2hi (A : Nat, B : Nat) -> Id Nat (Add A B) (Add A B) { Refl }; () }
example : progOk e2lo = true := by native_decide
example : progOk e2hi = true := by native_decide

-- E3. The structured neutral — §2.1's `IdCongr` mechanism — is unchanged by the
-- Π's binder case. An abstract function applied twice in a type position is ONE
-- term either way, which is what `Refl` inhabiting the `Id` says.
def e3lo : Term := prog{ fn E3lo (f : Π (x : Nat) → Nat, a : Nat) -> Id Nat (f a) (f a) { Refl }; () }
def e3hi : Term := prog{ fn E3hi (f : Π (X : Nat) → Nat, a : Nat) -> Id Nat (f a) (f a) { Refl }; () }
example : progOk e3lo = true := by native_decide
example : progOk e3hi = true := by native_decide

/-! ### E4. The two equalities are asymmetric, deliberately

    `Val.beq` is mode-blind because `convert` is built on it and §6 says case is
    inert under ⇝. `Term.beq` is STRUCTURAL, because its clients are not
    conversions: §18's `absOcc` abstracts occurrences by it, and a mode-blind
    version would match `⇝τ` against `τ` and abstract the marker away with the
    domain. (`FnDef.alphaEq`, the macro-vs-corpus round-trip criterion, was the
    second client and wanted the same thing for the same reason — a mode-blind
    version would let phase D's `fn` macro emit a differently-moded `FnDef` and
    still report equivalence. It retired in M28 cluster C with its one consumer;
    the asymmetry has one witness now instead of two.) Pinned because "one of
    these two is mode-blind and
    the other is not" is exactly the kind of asymmetry a later reader would
    otherwise assume was an oversight. -/

-- **The mode-blind equality is `Term.convEq` since M32 R1**, where it used to be
-- `Val.beq`. The asymmetry is the same one and it moved with the domain split:
-- conversion is what §6's "case is inert under ⇝" is about, so the unwrapping
-- lives in the equality `convert` is built on, and the structural `==` every
-- incidental comparison reaches for stays honest.
example : (Term.convEq (.cmpT (.const "Nat")) (.const "Nat")) = true := by native_decide
example : ((Term.cmpT (.const "Nat") : Term) == Term.const "Nat") = false := by native_decide

/-! ## §F. Modes at a VALUE callee — the shape phase C's `ih` stands on

    §7's recursor elaboration applies `ih` to a borrow and a proof at the
    predecessor (`ih ⟨left borrow⟩ H₁`), and `ih` is a Π-typed *variable* — "the
    sealed view at the predecessor". So the modes have to be readable off a Π
    that is a VALUE, not off a declaration's telescope, and the argument routing
    has to happen before the spine is consumed. That is what `binderModes` and
    `readArgsModed` are for, and this is where they are exercised.

    Note what the pair below is *not* testing: `hasType`'s λ-against-Π rule
    converts the domains, and conversion is mode-blind, so a λ written with
    lowercase binders inhabits a capital-bindered Π. The mode that governs the
    call is therefore the one on the type the CALLER sees — the seal's
    ascription. §5 point 4, arriving at binder modes: what you keep is what you
    write. F3 is that case on its own. -/

-- F1. A sealed callee with a capital binder: the argument is ⇝-read, so the
-- caller still holds its proof — twice over, and afterwards.
def f1 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- §2.4: the domains cite them
    let G = (λ (H : Le N0 M0). Z : Π (H : Le N0 M0) → Nat);
    let r = G(hnm);
    let s = G(hnm);
    hnm };
  () }
example : progOk f1 = true := by native_decide

-- F2. The lowercase twin of the same seal: the call MOVES the proof.
def f2 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- §2.4: the domains cite them
    let G = (λ (h : Le N0 M0). Z : Π (h : Le N0 M0) → Nat);
    let r = G(hnm);
    hnm };
  () }
example : progRejects f2 "holds ⊥" = true := by native_decide

-- F3. THE ASCRIPTION IS THE CONTRACT. The same lowercase-bindered λ, sealed at a
-- CAPITAL-bindered Π: accepted (conversion is mode-blind), and the call takes
-- its argument by ⇝, because the caller's view is the Π and nothing else.
def f3 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- §2.4: the domains cite them
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
  { let N0 = n; let M0 = m;                 -- §2.4: the domains cite them
    let G = λ (H : Le N0 M0). Z; let r = G(hnm); let s = G(hnm); hnm };
  () }
example : progOk f4 = true := by native_decide

-- F5. …and its lowercase twin moves, which is what says F4 is about the mode.
def f5 : Term := prog{
  fn Caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let N0 = n; let M0 = m;                 -- §2.4: the domains cite them
    let G = λ (h : Le N0 M0). Z; let r = G(hnm); let s = G(hnm); hnm };
  () }
example : progRejects f5 "holds ⊥" = true := by native_decide

/-! ## §G. Phase A's note 4, revisited with modes in hand — the rejection STANDS

    Phase A rejected a residual λ/Π after a saturated spine and recorded that
    this also rejects a function legitimately RETURNING a function, with "phase
    B's binder modes are what could distinguish them". They are not, and the
    reason is worth pinning rather than re-derived later.

    `Π (x : A) → (Π (y : B) → C)` and `Π (x : A) → Π (y : B) → C` are the SAME
    term. There is no residual binder whose mode belongs to one reading and not
    the other — the mode of the residual binder is a fact about how its own
    argument would be read, which is equally true under both readings. §6.3 is
    explicit about what the case decides: runtime existence of a BINDER, not the
    shape of a return type.

    The separating fact is elsewhere, and phase C/D may want it: a residual
    telescope with no borrow-moded binder could be curried soundly, because §12
    decision 4's reason for saturation is "a partial application at runtime is a
    closure holding its arguments — including, in general, borrows". That is a
    decision against a settled one, not a mode question, and it is left filed. -/

-- **FLIPPED at M32 R4**, with the reason recorded above at `Functions.c4`: a
-- comptime λ's partial application is a VALUE, because §12 decision 4 is a rule
-- about ⇒-ENTRY and a comptime capture holds no borrow. The refusal reached this
-- program only because `f(2)` and `f 2` were different nodes. Saturation is
-- still enforced where entry happens — `g2`/`g3` below, and `Functions.a5`.
def g1 : Term := prog{ let F = λ (x : Nat). λ (y : Nat). x; let z = F(2); () }
example : progOk g1 = true := by native_decide

-- The legitimate-return case, pinned as the LIMITATION it is: `mk` means to be
-- "the constant function at 1", and is refused.
def g2 : Term := prog{
  let Mk = (λ (x : Nat). λ (y : Nat). x : Π (x : Nat) → Π (y : Nat) → Nat);
  let k1 = Mk(1); () }
example : progRejects g2 "partial application" = true := by native_decide

-- Modes ARE expressible on such a Π — the elaboration is fine, the marker is
-- there — and change nothing, which is the point.
def g3 : Term := prog{
  let Mk = (λ (X : Nat). λ (y : Nat). X : Π (X : Nat) → Π (y : Nat) → Nat);
  let k1 = Mk(1); () }
example : progRejects g3 "partial application" = true := by native_decide

-- The route that DOES work today, so the limitation is bounded rather than
-- open-ended: a DECLARED fn may return a function (phase A's A6c). It is only
-- the value-callee spine that cannot say "stop here and hand me the rest".
example : progOk S26Seal.a6c = true := by native_decide

/-! ## §H. The flagship — `quicksort (fuel, v, Hfuel)` reads right

    §6's own sentence: "`fuel` lowercase (the body branches on it), `v` lowercase
    (borrow), `Hfuel` capital (cited in certificates, never scrutinized, never
    consumed)". Built on the existing decl-table path (J1, both worlds alive), so
    what it demonstrates is the SIGNATURE and the threading, not phase C's
    recursor.

    `Hfuel` is passed to a call that also takes the borrow, and then CITED — used
    to derive a certificate that the body goes on to use. Under phase A that
    sequence was unwritable without staging the proof into a λ before the call. -/

-- `step` is the callee of the flagship and of §H5/§H6; `stepLo` is H2's control,
-- the same callee with a RUNTIME proof parameter. Each appears in the chain of
-- every cohort that calls it.

-- **The `step` DECLARATION went in M28 cluster C**, and it is the last thing in
-- this file that was a `FnDef` rather than a program. It was kept as a value for
-- one reader — `S26Fn` §A's `roundTrips` battery, which held it against
-- `telePi`/`piPeel` — and it was that battery's only member with a CAPITAL binder,
-- so it was the member that said the round trip preserves the MODE MARKER and not
-- merely the binder count. The battery retired with the rest of §A's structural
-- probes, leaving this declaration with no reader at all.
--
-- **The mode claim did not retire with it**, and is carried by something better
-- than a round-trip property: the H1/H2 pair immediately below is a DIFFERENTIAL
-- over exactly this distinction. `qsish` declares `step` with a CAPITAL `H` and is
-- ACCEPTED — `Hfuel` is passed to the call and then cited afterwards, which is
-- only legal because a capital parameter is ⇝-read and so the call does not move
-- it. `qsishLo` is the same body against `stepLo`, whose proof parameter is
-- lowercase, and is REJECTED with "cannot be ⇒-moved". So if `telePi` dropped the
-- `⇝` marker on the way into the Π, `step`'s binder would be runtime, `qsish`
-- would become `qsishLo`, and the accepting half would go red. A round trip that
-- preserved binder count but not the marker is precisely what that pair catches.
--
-- (Note it is H1/H2 that does this, not H5: H5's two halves are BOTH rejected, on
-- purpose — it is the evidence that staleness is not a mode problem.)
--
-- The cohorts below declare their own `step` in their chains, which is where a
-- callee belongs now — including `qsish`'s, so the deleted declaration was a
-- duplicate of a callee already written three lines further down.

def qsish : Term := prog{
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn Qsish [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (Len *v) fuel) -> Unit
    { match fuel {
        Z => (),
        S(f2) => {
          Step(&m *v, S(f2), Hfuel);                       -- passed to a call…
          let Q = LeTrans (Len (old *v)) (S f2) (S f2) Hfuel (LeRefl (S f2));
                                                              -- …and cited AFTERWARDS
          UseLeC(Len (old *v), S(f2), Q);                     -- the derived certificate, used
          () } } };
  () }
example : progOk qsish = true := by native_decide

-- H2. THE CALLEE'S DECLARATION IS WHAT DECIDES. The same body against `stepLo`,
-- whose proof parameter is lowercase: the call would move an erased binder, and
-- the fence says so. Which is the right division of labour — a caller cannot
-- know whether a callee needs its proof at runtime, so the callee declares it.
def qsishLo : Term := prog{
  fn StepLo (v : &mut List Nat, b : Nat, h : Le (Len *v) b) -> Unit { () };
  fn UseLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn QsishLo [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (Len *v) fuel) -> Unit
    { match fuel {
        Z => (),
        S(f2) => {
          StepLo(&m *v, S(f2), Hfuel);
          let Q = LeTrans (Len (old *v)) (S f2) (S f2) Hfuel (LeRefl (S f2));
          UseLeC(Len (old *v), S(f2), Q);
          () } } };
  () }
example : progRejects qsishLo "cannot be ⇒-moved" = true := by native_decide

-- H3. …and `Hfuel`'s neighbour cannot be scrutinized, which is the other half of
-- §6's sentence: an erased index is erased, not merely copyable.
def qsishBad : Term := prog{
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

/-! ### H5. What modes do NOT fix, pinned so it is not mistaken for one

    A bound stated about `*v` is invalidated by any call through `v`: the call
    re-mints the payload, so the second `step(&mut *v, …, Hfuel)` wants
    `Le (Len σ') …` where `Hfuel` says `Le (Len σ_entry) …`. That is M23's
    opacity working exactly as designed (§2.2 — "the forgetting is wanted"), and
    it is why the real `quicksort` derives a fresh bound per recursive call
    rather than reusing one.

    The pair below is the evidence that this is NOT a mode problem: capital and
    lowercase proof binders are refused *identically*, with the same message
    about the same parameter type. Modes resolve R16 (consumption); they do not
    touch R12 (staleness), and nothing in §6 claims otherwise. -/

def h5hi : Term := prog{
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn H5hi (v : &mut List Nat, f : Nat, Hf : Le (Len *v) f) -> Unit
  { Step(&m *v, f, Hf); Step(&m *v, f, Hf); () };
  () }
def h5lo : Term := prog{
  fn Step (v : &mut List Nat, b : Nat, H : Le (Len *v) b) -> Unit { () };
  fn H5lo (v : &mut List Nat, f : Nat, hf : Le (Len *v) f) -> Unit
  { Step(&m *v, f, hf); Step(&m *v, f, hf); () };
  () }
example : progRejects h5hi "does not have its parameter type" = true := by native_decide
example : progRejects h5lo "does not have its parameter type" = true := by native_decide

/-! ### H6. The fence's boundary: a comptime binder is not RETURNABLE

    A function's result is a ⇒-value, so returning a capital binder is a move and
    the fence refuses it. Slightly surprising and entirely consistent — "usable
    only in ⇝-positions" includes the result position — and worth pinning because
    the natural reading of "citable after any call" stops just short of it.

    The pair also shows which end the R16 fix lives at. `h6lo`'s caller binder is
    RUNTIME and it works: the callee's capital parameter is what stopped the
    consumption, so a caller that genuinely owns a proof may pass it and still
    return it. Capitalizing the caller's own binder is a claim about the CALLER's
    erasure, and a returned value is not erased. -/

def h6hi : Term := prog{
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

/-! ## §I. Both machines, in lockstep (constraint 6)

    The comptime-argument rule is taken by the EXECUTING machine too, so the two
    agree on the observable the differential compares: what the caller still
    holds after the call. Exercised at a concrete argument and at a symbolic one
    (a call's fresh existential), through a decl-table call and through a value
    callee.

    The subject is a `List`, not a proof, and deliberately: a `Nat` or a proof
    spine is index-kind and already copies on read, so it could not tell the two
    modes apart. A `List` MOVES under ⇒ — which surfaces something worth naming:
    a capital DATA binder is ⇝-read, so the callee gets the value and the caller
    keeps it. That is silent aggregate duplication, which §2.1 explicitly refuses
    for lowercase binders ("Rust's line"). It is coherent only because the binder
    is ERASED — nothing is duplicated at runtime — and the FENCE is what makes
    that true, since the callee cannot observe it. The coherence rests on the
    fence, not on the read. -/

/-! `giveL` was the ONE declaration in this file that stayed a `FnDef`, and the
    reason was the EXECUTING machine rather than the checker: §I's differential
    runs each shape concretely, and a NULLARY `fn` lowers to a runtime λ binding
    nothing — which `λr` refuses ("a thunk makes ι ambiguous"). So a program that
    declares a nullary function checks (the seal mints a σ) but cannot be run, and
    I2's concrete side would fail before the relation was consulted.

    It rode in the `table` parameter until M28 D5 retired `decl{ }` and left no
    `FnDef` to put there. **It now takes an argument it does not use**, which is
    the smaller change and costs I2 nothing: what I2 needs is an argument that is a
    CALL'S FRESH EXISTENTIAL rather than a literal, and a call's result is minted
    fresh at any arity. The nullary wall is unchanged and recorded here rather than
    asserted — it fails at run time by design, so a test of it would be a test of
    `λr` refusing a thunk. -/

-- I1. Concrete: the capital call does not consume, so the list is still there.
def i1 : Term := prog{
  fn TakeLC (L : List Nat) -> Unit { () };
  let a = Cons(1, Nil); TakeLC(a); let b = a; () }
def i1lo : Term := prog{
  fn TakeL (l : List Nat) -> Unit { () };
  let a = Cons(1, Nil); TakeL(a); let b = a; () }
example : progOk i1 = true := by native_decide
example : progRejects i1lo "holds ⊥" = true := by native_decide
-- …and the environment says so directly: `a` survived the call and was moved by
-- the `let b = a` that follows it. `tailEnv` drops the program's own function
-- bindings, so the expected Ω is the one this assertion always had.
example : tailEnv i1 [("a", .bot), ("b", Val.cons (Val.nat 1) Val.nil)] = true := by
  native_decide

-- I2. Symbolic: the argument is a call's fresh existential rather than a literal.
def i2 : Term := prog{
  fn GiveL (u : Nat) -> List Nat { Cons(1, Nil) };
  fn TakeLC (L : List Nat) -> Unit { () };
  let a = GiveL(0); TakeLC(a); let b = a; () }
example : progOk i2 = true := by native_decide

-- I3. Through a VALUE callee, transparent and sealed.
def i3 : Term := prog{
  let a = Cons(1, Nil); let G = λ (L : List Nat). Z; let r = G(a); let b = a; () }
def i3s : Term := prog{
  let a = Cons(1, Nil); let G = (λ (L : List Nat). Z : Π (L : List Nat) → Nat);
  let r = G(a); let b = a; () }
example : progOk i3 = true := by native_decide
example : progOk i3s = true := by native_decide

-- The differential: the executing machine reaches the same Ω. `diffC` is phase
-- A's extended relation (σ-instance up to the pure fragment's own computation),
-- whose liveness was validated there — it says NO to a genuinely disagreeing run.
--
-- A shape is now the whole program, so three of the four carry an EMPTY table and
-- declare their callee themselves. The function binding shows up in both final
-- Ωs — sealed (a σ) on the checking side, the actual λ on the executing side —
-- and the relation binds the one to the other, which is the same σ-instance
-- reading it applies everywhere else.
def shapes : List Term := [i1, i2, i3, i3s]
example : shapes.all diffC = true := by native_decide

end Dllbc.Tests.S26Modes
end
-- └── end of what was `S26Modes.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S27Mixed.lean` ──────────────────────────────────────────────
section
/-!
# §27 (M27) — the mixed-return-type containment

**The hole, found by `dllbc-b1`'s back-probe** (branch `backprobe`,
`Tests/S27BackProbe.lean` §A, whose six witnesses this file's controls are drawn
from and credited to). A borrow-carrying return type is audited STRUCTURALLY —
`collectResultBorrows` walks it and checks each issued borrow against its owed
type — and is deliberately never pinned or `readC`'d, since `readC` rejects
`borrowT`. Both audit sites gate the value check on the WHOLE type being
borrow-free, so a non-borrow component of a borrow-carrying return type was judged
by nothing at all.

**Not vacuous — unsound.** The caller's `buildResult` mints a σ at the stated leaf
type regardless, so a caller RECEIVES the unearned claim as a proof and can return
it at its own value return type, where the pin-and-check path does run and passes,
because the σ genuinely carries that `sctx` type. b1 closed it: `fn closedBot ()
-> Bot`, no hypotheses, checking.

**Why it never bit.** No corpus declaration is both borrow-returning AND
ensures-carrying: cursor content rode in `back`, and backs ARE checked at their own
callee audit. M27 deletes backs and points the whole language at ensures, which
walks straight into it — so the containment lands before the conversion, not after.

**The containment.** Refuse a return type that MIXES borrow and non-borrow
components, at both dispatch sites, rather than teach the audit to judge value
components in a borrow-carrying position. A cursor's sayable contract is its issued
borrows' owed types; a value claim belongs on a value-returning function, where
§5 point 4's "what you keep is what you ascribe" is enforced by a check that looks.

**BOTH sites, and the second is the one that matters after M27.** The declaration
path (`checkFn`) and the SEAL path (`checkRFnBody`) carry the same gate, so a
sealed λ had the same hole. Fixing only `checkFn` would have left it in the path
the endgame keeps.
-/

open Dllbc
open Dllbc.StdLemmas (Len Le Znots)

namespace Dllbc.Tests.S27Mixed

/-! The `ok`/`rejects` helpers retired with the `FnDef` subjects they took (M28
    ν). Every subject in this file is a program now, and `progOk`/`progRejects`
    take one directly — which is also why the two imported subjects below
    (`S6Call.toNatProg`) reads the same as the local ones. -/


/-! ## §A. The break, contained — b1's witnesses, now refused

    `a1lie` is b1's A1: a cursor returning the head borrow beside a FALSE claim
    (`Id Nat Z (S Z)`) discharged by a `Refl` that cannot inhabit it. It CHECKED
    before this commit. -/

def a1lie : Term := prog{
  fn HeadLie (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat) → Id Nat Z (S Z)
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&m *hd, Refl)
        } };
  () }

example : progRejects a1lie "may not also carry VALUE components" = true := by native_decide

/-- b1's A5c, and **the control that makes the containment honest**: an HONEST
    claim in the same position is refused too.

    That is deliberate, not collateral. The position never judged anything, so
    acceptance there carried no information — a true claim was accepted for exactly
    the reason a false one was. Refusing both is what turns a silent lie into an
    explicit refusal; accepting the true one would mean the checker had started
    judging value components in a borrow-carrying position, which is the fix the
    containment declines to make. -/
def a5honest : Term := prog{
  fn HeadTrue (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat) → Id Nat Z Z
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => Pair(&m *hd, Refl) } };
  () }

example : progRejects a5honest "may not also carry VALUE components" = true := by native_decide

/-! ## §B. The two controls that isolate `hasBorrowT` as the whole cause

    b1's A2 and A5a. Neither changes here, and that is the point: the containment
    touches only the mixed position, so the rules that were already looking are
    left exactly as they were. -/

-- A2: the SAME false claim with no borrow in the return type. The pin-and-check
-- path runs, and always did.
def a2lie : Term := prog{
  fn ValLie (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : Nat) → Id Nat Z (S Z)
        { Pair(Z, Refl) };
  () }
example : progRejects a2lie "does not have return type" = true := by native_decide

-- A5a: the direct route to the same absurdity, refused as it always was.
def a5direct : Term := prog{
  fn Direct () -> Bot { Znots Z Refl };
  () }
example : progRejects a5direct "does not have return type" = true := by native_decide

/-! ## §C. Not over-broad: the shapes the corpus actually uses still check

    A containment that refused real cursors would be a regression wearing a fix's
    clothes. The two live shapes are a bare borrow and a Σ of borrows — `NthL`'s and
    `nth2`'s — and both are all-borrow, so neither mixes. -/

def bare : Term := prog{
  fn Bare (v : &mut List Nat, hi : Le (S Z) (Len *v)) -> &mut Nat
        { match v { Nil => botElim Unit hi, Cons(hd, tl) => &m *hd } };
  () }
example : progOk bare = true := by native_decide

def twoBorrows : Term := prog{
  fn Two (v : &mut List Nat, hi : Le (S Z) (Len *v))
        -> Σ (x : &mut Nat) → &mut List Nat
        { match v {
            Nil => botElim Unit hi,
            Cons(hd, tl) => Pair(&m *hd, &m *tl)
        } };
  () }
example : progOk twoBorrows = true := by native_decide

-- …and the whole corpus is unmoved: the full suite is green with the refusal in,
-- which is the claim `retMixesBorrow` has to earn — it must catch the break
-- without catching a single thing the corpus says today.

/-! ## §D. THE SEAL PATH HAS THE SAME HOLE, and this is the half that survives M27

    `checkRFnBody` gates its value check on `hasBorrowT ret` exactly as `checkFn`
    does, so a sealed λ ascribed at a mixed Π was unjudged in the same way. After
    M27 the seal is the ONLY audit site, so a containment that fixed only the
    declaration path would have fixed only the half being deleted. -/

def mixedSeal : Term := prog{ Π (v : &mut List Nat) → Σ (x : &mut Nat) → Id Nat Z (S Z) }

def sealProg : Term := prog{
  let F = (λ(v : &mut List Nat) { match v { Nil => (), Cons(hd, tl) => Pair(&m *hd, Refl) } } : %mixedSeal);
  () }

example : progRejects sealProg "may not also carry VALUE components" = true := by native_decide

-- Not vacuous: an all-borrow ascription in the same position is accepted, so the
-- refusal is about the MIXTURE and not about sealing a cursor at all.
def borrowSeal : Term := prog{ Π (v : &mut List Nat) → &mut List Nat }
def sealOk : Term := prog{ let F = (λ(v : &mut List Nat) { v } : %borrowSeal); () }
example : progOk sealOk = true := by native_decide

/-! ## §E. THE SECOND CONTAINMENT — a lie in a PARAMETER'S OWED TYPE

    b1 found a second closed `Bot`, and it is inside the first containment's
    blessing: the return type here is ALL borrow, so §A's refusal has nothing to
    say about it. The lie hides one level down, in what the parameter owes back.

    §6.1 exempts a borrow CONSUMED INTO THE RESULT from the payload audit — "being
    issued is its exemption" — and that is correct about the payload: a borrow that
    left in the result has no payload here to check. But the exemption takes the
    OWED TYPE with it, and the caller's group end then MINTS the captured loan's
    release AT that type. So the callee is excused from proving the claim and the
    caller receives it as fact. Neither end looks.

    **Refused rather than repaired**, on the same reasoning as §A: option (i) —
    "check the release against the owed type" — is vacuous as stated, since a
    freshly minted σ trivially has the type it was minted at. Making the unjudged
    position unwritable is the honest move. A parameter passed onward into the
    result owes back the type it was lent. -/

def e1lie : Term := prog{
  fn ThroughLie (v : &mut (s : List Nat ~> Id Nat Z (S Z))) -> &mut List Nat
        { v };
  () }
example : progRejects e1lie "would be checked by nobody" = true := by native_decide

/-- The isolating control: the SAME body and the SAME consumed-into-result shape
    with a TRIVIAL owed type is accepted. So the refusal is about the claim, not
    about handing a borrow onward — which is `through`'s whole job. -/
def e2trivial : Term := prog{
  fn ThroughOk (v : &mut List Nat) -> &mut List Nat { v };
  () }
example : progOk e2trivial = true := by native_decide

/-! ### E3. Measured before it shipped: the corpus's two non-trivial owed types

    The containment was run against the corpus before being committed, because a
    refusal that caught a load-bearing owed type would be a design conversation
    rather than a containment. Of **142 borrow parameters** in the corpus, exactly
    **two** carry a non-trivial owed type — and both are Unit-returning, so neither
    is ever consumed into a result and the exemption cannot fire on them. Their
    owed types are checked today and still are.

    That is the whole reason this ships as a containment: the position it closes is
    one the corpus never used, and the two places that DO state a rich owed type
    state it where the audit runs. -/

-- `to_nat (v : &mut (Bool ~> Nat))` — the type-changing ↝, S6Call's own subject.
example : progOk Tests.S6Call.toNatProg = true := by native_decide

/-! ### `swapS01` — the other rich owed type, moved here when `S16Spec` retired

    A spec-carrying in-place swap of positions 0,1, its `↝`-obligation the Σ
    `Σ (l : List Nat). Id Nat (Len l) (Len s)`. The cursor work stays inside ONE
    body (the contract-free interior, where collapse is transparent): the entry
    proof `LenSwapL 0 1 (*v)` is captured non-destructively; the two element
    cursors (h0 from v, h1 from its tail — disjoint by the suspension tree) swap by
    take-and-fill; `let l = *v` collapses the field loans TRANSPARENTLY to the
    swapped list; `*v := Pair(l, proof)` fills the Σ. The proof's type refines with
    the match (σ-bearing-state invariant), and the cursor output converges with
    `SwapL 0 1 s` by computation — so it type-checks against `Id (Len l) (Len s)`.
    The cursor writes and the pure specification agree, verified.

    It lives here because this section is the one that reads it: §E's containment
    is about owed types that are richer than a payload, and there are exactly two
    in the corpus. `S16Spec`'s remaining half was `chk` on library lemmas, every one
    of which has a consuming program elsewhere. -/

/-- `swapS01` as a PREFIX: it is the callee of everything below, and the caller is
    a plain statement block, so the S6Call idiom applies — a Lean function taking
    the rest and splicing it with `%`. (A cohort whose caller is itself a `fn`
    could not do this until M32 R4: two `%`-spliced chains both numbered their
    slots from `progBase` and collided by id. Both the arithmetic and the check
    are gone.) -/
def withSwapS01 (rest : Term) : Term := prog{
  fn SwapS01 (v : &mut (s : List Nat ~> Σ (l : List Nat) → Id Nat (Len l) (Len s)),
                    p : Le 2 (Len (*v))) -> Unit {
    let proof = StdLemmas.LenSwapL 0 1 (*v);
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
  %rest }

/-- The declaration alone, checked at its seal. -/
def swapS01 : Term := withSwapS01 prog{ () }
example : progOk swapS01 = true := by native_decide

-- Caller: borrow, call swapS01, demand the owner (recovering the Σ), open it to
-- l + the carried proof `pf : Id (Len l) (Len [1,2,3])`. The evidence survives the
-- opaque group-end — pf is in scope downstream though l itself is opaque.
def swapCaller : Term := withSwapS01 prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let b = &m x;
  SwapS01(b, ());
  let sig = x;
  match sig {
    Pair(l, pf) => { let m = l; () }
  } }

example : progOk swapCaller = true := by native_decide
-- The proof survives to the final env (pf ↦ a σ : Id (len l) (len [1,2,3])).
example : (match tailEnvs swapCaller with
  | [.ok env] => (env.lookup "pf").isSome
  | _ => false) = true := by native_decide

/-! ## §F. THE THIRD CONTAINMENT — reading a sealed borrow-taking function

    From c1's curry probe (branch `curryprobe`, `S27CurryProbe.lean` §G3, addendum
    `9b374c7f`), whose witnesses these controls are drawn from and credited to. It
    generalizes `S26Rec` §M in two ways that change the pricing:

    **1. No recursor is required.** §M found it on `ih` and read the trigger as
    something about induction hypotheses. It is not: the trigger is a σ whose Π is
    **borrow-moded**, which therefore has no `Val` (M26-C's founding fact) and lives
    in `fsig` alone, where `indexKindV`'s `.sym` case — which consults `sctx` — finds
    nothing and takes the move default. Any ordinary sealed borrow-taking function
    bound to a slot reproduces it.

    **2. It is not confined to the safe direction.** §M's case was reject-vs-run,
    which costs expressiveness and nothing else. c1 exhibits a program **both
    machines ACCEPT** whose final Ωs do not correspond — `f = ⊥` on the checking
    side, the λ-spine on the executing one. That is a simulation break on an
    accepted program: precisely what `S9Diff`'s whole-program assertions exist to
    catch, arriving where they cannot see it.

    So the position is made unwritable, checking-side only — the executing machine
    holds a real function value and copies it correctly, and refusing there would
    break running programs to protect a checker.

    **AND THE CONTAINMENT HAS SINCE GRADUATED INTO THE MODEL** (M27 α.2). The two
    paragraphs above are the record of what was believed and why, and both are
    still true of the mechanism — but the rule no longer keys on the mechanism.
    The ratified model is that **functions are reached by NAME**: the binding a
    declaration creates IS the name (§8), calling where bound and passing as an
    argument are name-uses, and the one move the model forbids is reading a
    function out of its slot into a SECOND binding, which is what turns it from a
    name into a value. So the key is now being a function at all, and the
    borrow-free case flips with it — c1 measured that one as SOUND on both
    machines (§G3a), and it is refused anyway, because soundness was never what
    made it wrong. What is left of "teach `indexKindV` about `fsig`" is §12 open
    8, which the model may simply not need.

    **AND THE MODEL HAS SINCE BEEN SUCCEEDED IN TURN** (M31 Stage A, §2.1). Read
    the three paragraphs above as the record they are: a mechanism, then a model,
    now a MODE. "Functions are reached by name" was a rule about the READ, and it
    had to be, because a function lived in a runtime slot where a second binding
    of it would be a second owner — which is exactly the divergence c1 measured.
    M31 makes a function binding comptime, and the premise goes rather than the
    symptom: a comptime binding is ⇝-read, erased and never ⇒-consumed, so `let G
    = F` copies knowledge, leaves `F` where it was, and creates no second owner
    for the two machines to disagree about.

    What is still refused is the LOWERCASE destination, and the tests below say so
    in pairs: `let g = F` is refused (by `fenceComptime` since M32 R3, which is
    where the rule it breaks lives), `let G = F` is
    accepted. Same programs rejected as under the previous two rules — the verdict
    has now outlived two complete changes of reason — but the needle is the FIX,
    which is the part a reader can act on. -/

def fSeal : Term := prog{ Π (v : &mut List Nat) → Unit }

-- F1. A sealed borrow-taking function, NO recursor anywhere, bound to a second
-- slot. This is the shape c1's §G3b has both machines accepting with different Ωs.
def f1read : Term := prog{
  let F = (λ(v : &mut List Nat) { () } : %fSeal);
  let g = F;
  () }
-- **The needle moved a THIRD time** (M32 R3), and this one is a deletion rather
-- than a rule change. `backstopFnRhs` existed for exactly this program: it fired
-- BEFORE the right-hand side was evaluated, because evaluating `F` hits
-- `fenceComptime` first, and its advice ("lower-case it") is wrong when the
-- value is a function. R3 deletes the backstop's scatter, so `fenceComptime` is
-- what refuses this now — the honest owner, since the rule the program breaks IS
-- erasure — and the advice was widened there to cover the case where
-- lower-casing is not the repair. Same program, same verdict, third message.
example : progRejects f1read "the binder to capitalise is the destination" = true := by
  native_decide

-- The migrated twin, which is the whole content of the change: capitalise the
-- second binder and the program is fine. c1's §G3b divergence cannot arise from
-- it, because a comptime binding is not a second OWNER — nothing was moved.
def f1readCap : Term := prog{
  let F = (λ(v : &mut List Nat) { () } : %fSeal);
  let G = F;
  () }
example : progOk f1readCap = true := by native_decide

-- F2. **THE ONE THAT FLIPPED, and it is the clearest statement of what changed.**
-- ~~The isolating control: a BORROW-FREE sealed function bound to a second slot is
-- ACCEPTED, because a borrow-free Π has a `Val`, its σ lands in `sctx` too, and
-- `indexKindV` can see it — so the refusal is about the missing value form, not
-- about functions.~~ **OVERTAKEN by α.2.** Every word of that is still true of the
-- MECHANISM, and c1 measured this program as copying correctly on both machines.
-- It is refused now anyway, and the reason is the model rather than a defect:
-- functions are names, and this reads one into a second slot. The refusal it gets
-- is the same one F1 gets, which is the point — there is no longer a class here to
-- be isolated from.
def gSeal : Term := prog{ Π (x : Nat) → Nat }
def f2read : Term := prog{
  let F = (λ(x : Nat) { x } : %gSeal);
  let g = F;
  () }
example : progRejects f2read "the binder to capitalise is the destination" = true := by
  native_decide

-- F2b. The ISOLATING CONTROL that survives, and it has to be a different one now:
-- an ordinary value in a second slot is still an ordinary read. So F1/F2 are about
-- functions and not about second bindings.
def f2data : Term := prog{
  let f = 3;
  let g = f;
  () }
example : progOk f2data = true := by native_decide

-- F3. And it does not touch CALLING, which under the model is the headline rather
-- than a caveat: calling where bound is a NAME-use. `.callV` locates its callee
-- rather than moving it (M26-E), so it never reaches the read rule at all.
def f3call : Term := prog{
  let F = (λ(v : &mut List Nat) { () } : %fSeal);
  let x = Cons(1, Nil);
  let b = &m x;
  F(b);
  () }
example : progOk f3call = true := by native_decide

end Dllbc.Tests.S27Mixed
end
-- └── end of what was `S27Mixed.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S26Fuel.lean` ──────────────────────────────────────────────
section
/-!
# §26 (M26-E) — paying §12 decision 8, shape by shape

The migration report's largest decline class was `[v]` payload decrease: a
recursion that shrinks a borrow's payload has no recursor form until §9's
borrow-mode eliminator exists, and §12 decision 8 blesses fuel-threading as the
interim. M26-D paid it for `partition` and M26-E for `append_back` — both the
LIST-cursor shape.

(§C found that most of that class was never in it, and M26-F adopted the
correction, which leaves the `[v]` class at 19 and a declared `back` as the
largest one. The sections below are as they were measured, each annotated where
the adoption changed what it says.)

This file pays it for the shapes that had not been paid, one per section, so that
"the interim is available" is a measured claim per shape rather than an
extrapolation from one. Each is a TWIN: the `[v]` original stays exactly as it is
(J1 — both worlds alive), and the migration is legible as a diff against it.

**What each section reports is the PRICE**, since that is the only thing still in
doubt. Decision 8 was taken knowing the surface cost; what nobody had measured was
whether the cost is uniform, and the answer so far is that it is not — the list
cursor costs a parameter and a dead branch, and the array cursor costs something
else (§B).
-/

open Dllbc
open Dllbc.StdLemmas (LeRefl Len Le)

namespace Dllbc.Tests.S26Fuel

/-! **`bothWays` is gone** (M28 D6). It read "assemble this declaration's cohort
    into a program and check it" — the surviving half of a pair whose other half
    (`checkFn` on the declaration) died in M27-δ, leaving the half that was always
    the one in doubt: decision 8's question was whether the fuel-threaded interim is
    AVAILABLE at all, not whether two checkers agree about it. Every subject it took
    is a `fn` chain now, and `progOk` says the same thing about one directly. -/

/-! ## §A. The LIST cursor: `zero_all`

    `zero_all` walks a list through a mutable borrow, zeroing each element, and
    passes the tail's field reborrow to itself. It is the shape §7 cost 4 names as
    having "no easy recursor form" — no counter at all — and the one S6Call and
    S23Direct both carry. -/

def zeroAllF : Term := prog{
  fn ZeroAllF [fuel] (fuel : Nat, v : &mut List Nat, Hf : Le (Len *v) fuel) -> Unit {
    match v {
      Nil => (),
      -- The dead branch, the same ex-falso the other two migrations carry:
      -- `Hf : Le (S (Len *tl)) Z` IS `Bot`.
      Cons(hd, tl) => match fuel {
        Z => botElim Unit Hf,
        S(f2) => { *hd := 0; ZeroAllF(f2, tl, Hf); () }
      }
    } };
  () }

example : progOk zeroAllF = true := by native_decide
-- The `[v]` original is untouched and still DECLINES, and the decline is asserted
-- where the function lives: `S6Call.zeroAll` is a program now (M28 D6), rejected
-- on `fnRefusedNeedle`, on "§12 decision 8" by name, and with `progOk = false` to
-- say the sentinel fires at the binding rather than at a call.
-- (The `fnElab`-return-value assertion that used to sit here went in M28 cluster
-- C, as one of the granular meta-assertions the e2e rule retires.)

/-! ## §B. The ARRAY cursor was already paid, and the corpus says so

    `walkArr [a]` recurses on a carved sub-slice and S24 pins its REJECTION, with
    the finding beside it: "§8's guard compares the actual against the parameter's
    current snapshot by `strictSubterm`… a carve's body split refines the payload
    σ to an `arrCat` SPINE, so from that moment no sub-slice is a structural
    predecessor of its parent… array recursion stays fuel-carried."

    So there is nothing to migrate here, and I nearly wrote the twin before
    checking: `walk` IS `walkArr` with `[fuel]` in place of `[a]` and the same body
    character-for-character. It was written at the time, it checks, and it
    MIGRATES. The array shape's decision-8 price was paid in M24, before decision 8
    existed.

    What the migration report shows for `walkArr` is therefore the two paths
    agreeing about a program neither accepts: the declaration path REJECTS it at
    the guard, the macro DECLINES it at `[a]`-on-a-borrow, and the reasons are the
    same fact seen from two sides. -/

-- **The field-by-field comparison went in M28 cluster C**, with the `.dec`
-- comparison beside it. Two `FnDef` records agreeing on `telescope`/`retType`/
-- `body` (up to `renameSelf`) and differing on `dec` is a structural
-- meta-assertion, and the e2e rule retires those; what it was EVIDENCE for is the
-- sentence above, which the two verdicts below carry between them — one form
-- checks, the other declines, and the source shows they are the same function.
-- ~~`bothWays walk`~~ — both halves are asserted where the two functions are
-- written (M28 D6). `S24Arrays.walk` is `progOk`, `S24Arrays.walkArr` is
-- `progRejects` on the refusal needle and on "§12 decision 8", and the two sit
-- adjacent in that file differing in the HINT alone, which is what makes the pair
-- about `[a]`-on-a-borrow rather than about the body.

/-! ## §C. THE FINDING: most of the `[v]` class needs no fuel at all

    §7 demotes `[k]` to a **scrutinee-selection hint**, and that changes what a
    mis-chosen one costs. The declaration-era guard was happy with `[v]` whenever
    the payload decreases — which it does — so there was never a reason to name
    anything else, and `NthL`/`nth2` name the borrow. But they ALSO decrease on
    their INDEX, which is a `Nat`, and the macro serves that directly.

    **Correcting the hint is free.** No fuel, no signature change, no caller
    change, no dead branch — the same body, the same telescope, the same return
    type, one field of the `FnDef` different. The bound descends definitionally
    exactly as it did (`p : Le (S (S k)) (S (Len *tl))` IS `Le (S k) (Len *tl)` —
    M14's own bounds-cursor property), which is why nothing else moves.

    With two hints corrected the WHOLE S14 family migrates: four accepted on both
    paths, one rejected on both (its negative control), nothing declined. That was
    five declines a moment ago, and it was the third-largest block in the map.

    This is the same shape as M26-C's `split_off` observation — "it needs NO fuel,
    because it recurses on its index, which is already a `Nat`" — arriving as a
    general fact about the class rather than as a property of one function. What
    genuinely needs fuel is narrower than the report suggested: a cursor with NO
    decreasing argument of its own (§A's `zero_all`, and `recCursor`, which is the
    same function under another name).

    **M26-F ADOPTED this**, so the section reads differently than it did when it was
    written. `NthL`/`nth2` in S14Bounds and S17Spec now declare `[i]` at the source,
    and the twins below are no longer twins — each is equal to the corpus
    declaration it was a correction of. The measurements stay because what they
    pin is still a claim: that the hint is the ONLY thing that moved, and that the
    declaration path is as happy with `[i]` as it was with `[v]` (M14's descent
    accepts index decrease either way, so nothing in S14 or S17 needed re-proving).

    The two round-trip mirrors of `nthS` moved with it (`SDeclMacro.nth'`,
    `SDeclUnified.nthU`), and only one of them noticed: `FnDef.alphaEq` as it then
    stood compared name/telescope/retType/body/back and NOT `dec`, so the `alphaEq`
    mirror stayed green against a stale hint while the exact-`BEq` mirror went red.
    (M27-δ widened the criterion to see `dec`; both mirrors and the criterion itself
    have since retired — the criterion in M28 cluster C, with its one consumer.) -/

-- **`nthI`/`nth2I`/`p14fixed` and their equality assertion went in M28 cluster C.**
-- They were `{ S14Bounds.nth with dec := some 1 }` and a copy of `p14` built from
-- them — the corrected hint SIMULATED in the harness — and the assertion beside
-- them said "nothing changed but the hint". M26-F adopted the correction at the
-- source, at which point each alias was `==` to the declaration it aliased, the
-- pool copy was `==` to `S26Migrate.p14`, and both assertions had become
-- structural comparisons of a record with itself. The subjects below are the
-- corpus declarations directly, which is what the aliases had turned into.
-- **And those two went the same way in M28 D6**: `S14Bounds`'s cursor family is
-- one `fn` chain now, `progOk` on itself, so restating its verdict here would be
-- the third copy of one fact. What this section asserts is the FINDING, and the
-- finding is legible in the source it describes — `NthL`/`nth2` say `[i]`.

/-! The whole family, hints corrected: 4 accept, 1 rejects (`rejectProbe` is S14's
    own negative control), NOTHING declines. It was a verdict VECTOR read off
    `S26Migrate.p14` — positional, so it said WHICH one rejects where a tally only
    said that one does, and a `none` would have been a decline.

    **The vector retires with the pool** (M28 D6): S14's five are five programs in
    that file now, four `progOk` and one `progRejects`, which is the same claim with
    the identity attached to each verdict instead of to a position. A decline cannot
    hide there either — a `fn` the lowering refuses is rejected on
    `fnRefusedNeedle`, not accepted. Before M26-F's adoption the same five functions
    declined five times (`report p14 == R 0 0 5`, S26Migrate §Y as it then read). -/

/-! ## §D. What is left needing fuel, and one macro gap this section found

    After §B and §C the `[v]` class is: `zero_all` and `recCursor` (the same
    function, twice in the corpus) — a cursor with no decreasing argument but the
    payload — plus S17/S19's `NthL`/`nth2`/`swapS`, which since M26-F carry the
    corrected hint (or, for `swapS`, never had one) and are blocked by their
    declared `back` alone. §A pays the first; the second waits on the `back`
    question, which is now the only thing standing under 49 declarations.

    And one thing that LOOKS like a macro gap and is not, recorded because I added
    a refusal for it before thinking it through and then took it out again:
    `fnElab` with no `[k]` emits a plain sealed λ without checking that the body
    has no self-call, so `zero_all` with its hint simply REMOVED elaborates
    happily. The resulting program is still rejected — and by §8's OWN mechanism,
    which is the point: the `let` is not in scope in its own right-hand side, so
    the self-call resolves to nothing and falls through as the forward reference it
    is. M26-C pinned exactly that as why `bad()` is unwritable ("not by a recursion
    rule; the binding is not in scope in its own right-hand side"), and a macro
    refusal would paper over the demonstration. -/

-- `zero_all` with its hint simply REMOVED, written as a program (M28 cluster C —
-- it used to be `fnElab` on a record update, wrapped in a hand-built `letIn`).
-- `FnStmt` §E is the same function WITH the hint, refused at decision 8; the two
-- sit either side of the distinction this paragraph is about.
def noHintStmt : Term := prog{
  fn ZeroAll (v : &mut List Nat) -> Unit {
    match v { Nil => (), Cons(hd, tl) => { *hd := 0; ZeroAll(tl); () } } };
  () }
example : progRejects noHintStmt "unknown function" = true := by native_decide
-- Not vacuous: the same body WITH a hint (and the fuel §A threads) is a program
-- that CHECKS, so the rejection above is about the missing recursor and not about
-- the body.
example : progOk zeroAllF = true := by native_decide

/-! ## §E. The map, re-measured — and the two blockers COMPOSE

    §C's finding is worth a number over the whole corpus rather than over one
    family, and the number is not what either fix predicts on its own. As measured
    before M26-F adopted the hints:

        73 declines as the corpus stood
        68 with the two hints corrected          (−5)
        65 with `back` stripped                  (−8)
        20 WITH BOTH                             (−53)

    The corpus now stands at the second line, so what the assertions below measure
    is 68 and 19 — one better than the 20 predicted, because `S19Partition.nth2Lie`
    is written `{ nth2S with … }` and inherited the corrected hint, which the
    name-matching `fixHints` never reached. That is the one place where adopting a
    fix at the source does more than simulating it in the harness.

    Neither fix alone does much and together they collapse the map, because a
    cohort is a CLOSURE: one un-migratable leaf declines everything above it. S17's
    `NthL` has both a declared `back` and a `[v]` hint, so fixing either leaves it
    declining, and everything in S17 and S19 that reaches it declines with it.
    "Fix the biggest class first" is exactly the wrong strategy against a closure —
    the blockers have to come off together or the report barely moves, which is why
    two rounds of measurement made the map look stubborn and the third made it
    small.

    What survives both fixes is 19, and it is the honest residue: 17 in S23 (the
    true `[v]` cursors — `partition`, `append_back`, `recCursor`, `partitionLoses`
    — everything whose closure reaches one of them, the guard twins, and
    `recDeep`), `zero_all` in S6 (paid in §A), and `walkArr` in S24 (a negative
    control, §B). S19's `nth2Lie` was the twentieth and left with the adoption.

    **Stripping `back` is NOT free** — it removes a mechanism a caller relies on,
    which is the design question that goes to the user. Correcting a hint IS free.
    The measurement separates them so the question can be asked about eight
    declarations rather than about the corpus. -/

/-! ### The corpus-wide CENSUS retired here (M28 μ)

    Four assertions counted `S26Migrate.pools` — total declines, total
    accepts/rejects, the per-pool decline vector, and that `fixHints` was a no-op on
    every pool — together with the `fixHints`/`fixAll` harness they were computed
    through. They are gone, and the reason is not that they were failing.

    **A census of `FnDef` pools has no subject once the record form is gone.** `fn`
    is a statement of the program grammar now (M28 θ), the corpus is being rewritten
    onto it, and a declaration that becomes a program leaves the pools — so every
    migrated file moved these numbers for a reason that had nothing to do with any
    verdict changing. Kept through the sweep they would have been ~24 manual
    recomputes and a standing invitation to "fix" a red build by editing a constant.

    What they were FOR survives in two stronger forms, neither of which counts:

      * **The residue by NAME** (`S27Dispose` §B) — the same nineteen declarations
        the decline count summarised, pinned name for name, so one appearing or
        vanishing goes red with its identity attached.
      * **Per-declaration verdicts** — §C above, positional, which is what the
        p14 tally became.

    `fixHints` went with them: it corrected `NthL`/`nth2`'s `[k]` hint, M26-F adopted
    the correction at the source, and the assertion that it had become a no-op was
    one of the four. That claim is now structural — there is no `fixHints` to be a
    no-op — and it is checked where it still bites, by `S27Dispose`'s residue list
    (computed without it) not moving. -/

end Dllbc.Tests.S26Fuel
end
-- └── end of what was `S26Fuel.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S26Prog.lean` ──────────────────────────────────────────────
section
/-!
# §26 (M26-E) — programs are terms

`combining-fns.md` §8: **a program is an arbitrary term, and running it is
⇒-evaluating it.** A module is a let-chain — transparent lets, sealed lets, a
tail — and checking it is the symbolic ⇒-walk of the same term. `FnDef` is what
this deletes.

Three claims are tested here, and the third is the one that needed a kernel rule:

  1. **The walk is the check.** `checkProgram` is `explore` plus the audit of each
     path's result; each sealed `let` fires its audit once, at its own node, in
     program order. Nothing new — §5 put the audit at the node in M26-C, and a
     let-chain is what puts the nodes in order.
  2. **Scope is the call table.** A callee is a binding lexically above the call,
     and the surface has resolved `f(…)` that way since M26-A. So a program is
     checked against NO table, and a forward reference is unwritable rather than
     rejected: a let-chain cannot reference downward.
  3. **§7 cost 2's "and globals" acquires a referent.** Until now a runtime λ's
     body had to be closed, because its callees lived in the table and were
     reached by name. With the table gone they are variables, so a body's free
     variables are its callees — admitted when they name a FUNCTION bound above,
     refused otherwise (capture stays deferred, constraint 5). Both machines
     needed it: the checking side seeds them through frame isolation, the
     executing side keeps their ids out of the frame shift.

**Both machines, every program.** Per §12 decision 7 and constraint 6, each
program below is CHECKED and RUN, and the differential — the merged relation of
M26-C — is asserted on it. A checking-side claim about a program that was never
run is exactly what the polarity doctrine forbids.
-/

open Dllbc
open Dllbc.StdLemmas (LeTrans LeRefl LeUpR IdCongr Append Len Le)

namespace Dllbc.Tests.S26Prog

/-! ## Helpers

    `progOk`/`progRejects`/`runProgram` are `Program.lean`'s. The differential is
    S9Diff's merged relation, applied to a program instead of to a `FnDef` body —
    which is the same thing now, and the reason `diffC` needed no new definition:
    it already took a TERM. -/

-- (`progDiff` moved to `S9Diff` in M28 D10 — the differential is that file's
-- subject, and this file is one of two consumers.)
open Dllbc.Tests.S9Diff (progDiff)

/-- The walk WITHOUT the end-of-scope demand — for showing that `endScope` is not
    vacuous (it is the difference between a parked loan and a released value). -/
def rawEnvs (t : Term) : List (Except String Env) :=
  (explore defaultFuel (atBoundary t) initSt).map
    (fun r => r.map (fun p => canonicalize p.2.env))

/-! ## §A. A program is a term

    The smallest complete statement of §8: no `FnDef`, no telescope, no return
    type to declare — a let-chain and a tail, checked by one walk and run by the
    other. -/

-- A1. Transparent lets and a tail. The tail is checked in the ACCUMULATED Ω,
-- which is what makes `retType` a real demand site rather than decoration.
def a1 : Term := prog{ let x = 3; let y = S(x); y }
example : progOk a1 (.const "Nat") = true := by native_decide
example : progRejects a1 "does not have return type" (.const "Bool") = true := by native_decide
-- `x` survives its own use: a `Nat` is index-kind, so §2.1's copy-on-read leaves
-- the owner intact where data proper would be moved out.
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
example : progOk a2 (.const "Nat") = true := by native_decide
example : progDiff a2 = true := by native_decide
-- The claim that it was really the seal that made `f` callable: the same program
-- with `f` bound to a NON-function is refused, and the refusal names the capture.
def a2cap : Term := prog{
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

/-! ## §B. Each sealed `let` fires its audit ONCE, at its own node, in program order

    §8's sentence about checking, taken apart into the three things it claims. The
    audit is at the BINDING (not at a use), it happens whether or not there is a
    use, and the order the lets are written is the order the audits run. -/

-- B1. A sealed function that does not inhabit its ascription is refused AT ITS
-- OWN `let`, with nothing downstream of it — the binding is the demand site,
-- which is what "the audit is the checking of the seal" means (§5).
def b1 : Term := prog{ let F = (λ(x : Nat){ x } : Π (x : Nat) → Bool); () }
example : progRejects b1 "does not have return type (Bool)" = true := by native_decide

/-- ### B2. The vacuous twin, kept beside it

    An UNSEALED λ with the same nonsense body is ACCEPTED, because nothing demands
    it: `readR` forms the value and never looks inside. This is phase A's
    per-DEMAND-SITE finding, and it is the trap a reader of B1 would otherwise
    fall into — "binding a bad function is caught" is true only of a SEALED
    binding. The live twin below is what makes it a real difference: call it, and
    the demand arrives. -/
def b2vac : Term := prog{ let G = λ(x : Nat){ True }; () }
def b2live : Term := prog{ let G = λ(x : Nat){ True }; let r = G(1); r }
example : progOk b2vac = true := by native_decide
example : progRejects b2live "does not have return type (Nat)" (.const "Nat") = true := by native_decide

-- B3. **Program order**, pinned the only way it can be: two lies, and the one
-- that is reported is the FIRST. (Both messages have the same shape, so the
-- needles are the types, which differ.)
def b3 : Term := prog{
  let F = (λ(x : Nat){ x } : Π (x : Nat) → Bool);
  let G = (λ(x : Nat){ True } : Π (x : Nat) → Unit);
  () }
example : progRejects b3 "does not have return type (Bool)" = true := by native_decide
example : progRejects b3 "does not have return type (Unit)" = false := by native_decide

/-! ## §C. Scope is the call table

    "A caller sees exactly the bindings lexically above it, so the checker's
    callee-resolution table and its assembly disappear." Every program in this
    file is checked against an EMPTY table (`checkProgram`'s default), which is
    the positive half of that claim. Here is the rest. -/

/-- ### C1. No forward references — unwritable, not rejected

    A let-chain cannot reference downward, so `h` in `g`'s body does not resolve
    to the `h` bound below: it resolves to nothing, and falls through to the
    (empty) table. Nothing implements this rule — it is what scope IS, which is
    why §8 can say mutual recursion "becomes unwritable" rather than "stays
    rejected". Note WHERE it is caught: at `g`'s own seal, because the audit is at
    the binding, so the diagnosis does not wait for a call. -/
def c1 : Term := prog{
  let G = (λ(y : Nat){ H(y) } : Π (y : Nat) → Nat);
  let H = (λ (x : Nat). x : Π (x : Nat) → Nat);
  () }
example : progRejects c1 "unknown function 'H'" = true := by native_decide
-- …and the same program with the two bindings SWAPPED is accepted, so the
-- rejection is about the order and not about the pair.
def c1ok : Term := prog{
  let H = (λ (x : Nat). x : Π (x : Nat) → Nat);
  let G = (λ(y : Nat){ H(y) } : Π (y : Nat) → Nat);
  let r = G(3);
  r }
example : progOk c1ok (.const "Nat") = true := by native_decide
example : progDiff c1ok = true := by native_decide

/-! ### C2. The deliberately-wrong table becomes a different let-prefix

    The old suite guarded caller-side reasoning by checking a caller against a
    table entry whose signature was a lie. There is no table to lie in now, so the
    same test becomes **one program under two signatures**: the callee's body and
    the caller that uses it are identical and honest in both, and what differs is
    the type the body is SEALED at. That is §5 point 4 with nothing left to
    interpret — what the caller keeps is what the programmer wrote — and it is a
    sharper test than the old one, because the lying version is a program that
    itself checks. -/

/-- The whole program, parameterised by the ONE thing the pair differs in. Body
    and caller are shared by construction rather than by two copies agreeing, so
    the difference the test measures is the only difference there is. -/
def c2under (sig : Term) : Term := prog{
  let F = (λ(n : Nat){ Pair(n, Refl) } : %sig);
  let r = F(3);
  r }
/-- The retType the program is demanded at: the equation the caller wants. -/
def c2demand : Term := prog{ Σ (m : Nat) → Id Nat m 3 }

/-- A — the signature CARRIES the equation. -/
def c2keeps : Term := c2under (prog{ Π (n : Nat) → Σ (m : Nat) → Id Nat m n })
/-- B — the same body, sealed at a type that FORGETS it (true, and useless). It
    checks: the lie is not in the callee, it is in what the callee promises. -/
def c2forgets : Term := c2under (prog{ Π (n : Nat) → Σ (m : Nat) → Id Nat m m })

example : progOk c2keeps c2demand = true := by native_decide
example : progRejects c2forgets "does not have return type" c2demand = true := by native_decide
-- Not vacuous: the forgetting prefix is a program that checks on ITS OWN terms —
-- at the weaker demand its callee's signature does support. So the rejection
-- above is about what was kept across the seal, and not about the program being
-- broken.
example : progOk c2forgets (prog{ Σ (m : Nat) → Id Nat m m }) = true := by native_decide
-- The keeping prefix does NOT also satisfy the weaker demand, which is worth a
-- line because it is the honest reading of "what you keep is what you write":
-- there is no subsumption here, only conversion — a σ has the type it was minted
-- at, and `Id Nat m 3` and `Id Nat m m` are different types even though the first
-- is the more informative claim about this particular callee.
example : progOk c2keeps (prog{ Σ (m : Nat) → Id Nat m m }) = false := by native_decide

/-! ## §D. Globals: the one kernel rule this phase needed

    §7 cost 2 admits "closed" function values — "arms reference only their own
    binders **and globals**" — and until now the second half was empty, because
    the callees lived in the table. §8 puts them in scope, so a body's free
    variables ARE its callees, and the closedness premise had to learn the
    difference between naming a function above you and capturing your
    environment. `admitGlobals` is that line, and it is drawn at what the body can
    DO with the binding: a function is CALLED (a place read — the callee is
    located, never moved), while data is moved, borrowed or written.

    Both machines needed something, and neither needed the other's: the checking
    side seeds the admitted bindings through frame isolation (a sealed body's Ω is
    otherwise fresh), the executing side keeps their ids out of the frame shift
    (`shiftVarsK`) so a reference to `#901` still finds `#901` inside a frame. -/

-- D1. Two frames deep: `h` calls `g` calls `f`, each a binding above it. This is
-- what says the keep set survives NESTING — the innermost body is entered through
-- two frame shifts, and both globals are still where the program put them.
def d1 : Term := prog{
  let F = (λ (x : Nat). S(x) : Π (x : Nat) → Nat);
  let G = (λ(y : Nat){ F(F(y)) } : Π (y : Nat) → Nat);
  let H = (λ(z : Nat){ G(G(z)) } : Π (z : Nat) → Nat);
  let r = H(0);
  r }
example : progOk d1 (.const "Nat") = true := by native_decide
-- The executing machine agrees, and on the VALUE: four applications of successor.
example : (match runProgram d1 with
           | .ok env => env.lookup "r" == some (Val.nat 4)
           | .error _ => false) = true := by native_decide
example : progDiff d1 = true := by native_decide

/-- ### D2. What is still refused, per capture kind

    Constraint 5 defers environment capture wholesale, and it stays deferred:
    admitting functions is not admitting environments. Each refusal is paired with
    the same program passing the thing IN, so the rejection is about the capture
    and not about the program. -/

-- D2a. DATA. (M26-C's a3bad, now with the message that says which of the two
-- things went wrong — it names a binding in scope, and that binding is not a
-- function.)
def d2data : Term := prog{
  let n = 3;
  let G = (λ(a : Nat){ let z = n; a } : Π (a : Nat) → Nat);
  () }
def d2dataOk : Term := prog{
  let n = 3;
  let G = (λ(a : Nat, m : Nat){ let z = m; a } : Π (a : Nat) → Π (m : Nat) → Nat);
  let r = G(1, n);
  r }
example : progRejects d2data "a runtime (lowercase) binding" = true := by native_decide
example : progOk d2dataOk (.const "Nat") = true := by native_decide

-- D2b. A BORROW — the case constraint 5 is really about, since a captured borrow
-- is a suspended loan with no scope to end it in.
def d2borrow : Term := prog{
  let l = Cons(1, Nil);
  let b = &m l;
  let G = (λ(a : Nat){ *b := Nil; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d2borrow "a runtime (lowercase) binding" = true := by native_decide

-- D2c. A free variable that names NOTHING is a different rejection with a
-- different message, and it is the one §8 explains: a let-chain cannot reference
-- downward. (Reached here through a `.callV`-free body, so it is the variable
-- rule and not the call rule doing the work — c1 covers the call side.)
def d2free : Term :=
  .letIn ⟨0, "g"⟩ (.seal 0 (Term.lamTel [(⟨1, "a"⟩, .const "Nat")] (.letIn ⟨2, "z"⟩ (.var ⟨9, "nope"⟩) (.var ⟨1, "a"⟩)))
    (prog{ Π (a : Nat) → Nat })) .unit
example : progRejects d2free "not bound anywhere above it" = true := by native_decide

-- D3. A sealed PROOF is not a global either, and that is deliberate rather than
-- an oversight: §5's `Qed` binding is a value, and a body that wants it should
-- take it as a capital parameter (which is exactly what §6 built). Recorded as a
-- limitation with its route beside it, not as a defect.
def d3 : Term := prog{
  let cert = (LeRefl 3 : Le 3 3);
  let G = (λ(a : Nat){ let z = cert; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d3 "a runtime (lowercase) binding" = true := by native_decide

-- D3b. **The capital form of the same binding is now ACCEPTED** (M31 Stage A),
-- and this test is the clearest statement of the rule that makes Stage A
-- possible at all.
--
-- It used to be refused, on the ground that `let X = e` reads `e` under ⇝ while
-- the seal is a ⇒-form because minting needs an event — so "sealed" and
-- "comptime-bound" were mutually exclusive, and `let Cert = (… : …)` as a `Qed`
-- form was told which half to drop. M31 dropped neither, by making the seal's
-- arrow a property of the SEAL as well as of the binder (`Var.comptimeRhs`) — the
-- event still happened under ⇒, and what the capital binder changed was the
-- binding. **M32 R3 removes the carve-out that bought that** (`Var.comptimeRhs`
-- is gone): the seal is ⇝-evaluable now, because its σ is the one its SITE has at
-- its inputs rather than a fresh one, so a capital `let` reads it under ⇝ like
-- everything else and the arrow is the binder's case with nothing left over. Same
-- program, same verdict, one fewer exception.
--
-- This is not a concession made for proofs; it is forced. `fn F …` desugars to
-- exactly this term — a comptime `let` of a λ ascribed its Π (§2.1) — so a rule
-- that refused `let C = (t : T)` would refuse every function declaration in the
-- language. The `Qed` binding and the function declaration are the same form, and
-- M31's answer for one is its answer for both.
--
-- D3 above is UNMOVED, and the pair is worth reading together — but note WHY it
-- is unmoved, because the reason changed under it. D3's `cert` is refused for
-- being LOWERCASE: that is the citation rule (§2.4) reading the binder's mode,
-- not the old value-directed test that admitted function VALUES and refused
-- proofs (`globalKind`, which Stage A superseded and Stage C deleted). Under the
-- rule as it now stands a proof bound CAPITAL *is* citable from inside a body,
-- so "captured" changed too, and D3c below pins it rather than leaving it to be
-- inferred from this paragraph.
def d3cap : Term := prog{ let C = (LeRefl 3 : Le 3 3); () }
example : progOk d3cap = true := by native_decide

-- D3c. The citation half, which D3/D3b together imply and neither checks: the
-- capital proof CITED from inside a λ body, at a ⇝ position. Accepted — this is
-- what `globalKind`'s deletion means operationally, since the predicate would
-- have refused it (a `Le 3 3` σ is not a function value).
def d3cite : Term := prog{
  let C = (LeRefl 3 : Le 3 3);
  let G = (λ(a : Nat){ LeUpR 3 3 C } : Π (a : Nat) → Le 3 (S 3));
  () }
example : progOk d3cite = true := by native_decide

-- And the ⇒ half is still shut, which is why "citable" is not "usable anywhere":
-- `let z = C` inside the body MOVES a comptime binder, and the fence takes it
-- before §2.4 is consulted. Capture is open; consumption is not (§8 non-goals).
def d3move : Term := prog{
  let C = (LeRefl 3 : Le 3 3);
  let G = (λ(a : Nat){ let z = C; a } : Π (a : Nat) → Nat);
  () }
example : progRejects d3move "cannot be ⇒-moved" = true := by native_decide

/-! ## §E. The end of a program is a demand on everything it still holds

    A program that lends a local and never looks at it again leaves the loan
    parked: the checking machine releases a group when something demands it, and
    nothing does. The executing machine releases a frame's loans on the way out.
    Without `endScope` the two would end in visibly different Ωs on an ordinary
    program — so this is not tidiness, it is the differential's precondition, and
    it is shown as a difference rather than asserted. -/

-- E1. The raw walk leaves the loan parked…
example : (rawEnvs push).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .loanM _ => true | _ => false)
    | .error _ => false) = true := by native_decide
-- …and the ended one has released it into a σ, which the concrete list then
-- instantiates (that is why §A's `progDiff push` is green).
example : (programEnvs push).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => v.symOf?.isSome)
    | .error _ => false) = true := by native_decide

/-! ## §F. The flagship — RETIRED HERE (M28 D3), because the source is fuel-threaded

    M23's in-place quicksort — `Sorted` and the permutation count equation over the
    exit snapshot, no declared `back` anywhere in the call tree — assembled as three
    sealed lets and a tail, checked against no table and run to a sorted list. That
    was this milestone's acceptance test, and it needed a MIGRATION to exist:
    `partition` and `append_back` were written with `[v]`, which has no recursor
    form, so this section fuel-threaded `append_back` by hand, retargeted
    quicksort's two call sites with a term-rewriting pass (`toP`/`migrate`), and
    assembled `[partitionF, appendBackF, quicksortP]` with `progOf`.

    **The migration has been adopted at the source** (M28 D3). `S23Direct` stage
    (vi) is that cohort, written once as one `fn` chain in the surface — the
    fuel-threaded `partition` that lived in `S26Fn`, the `append_backF` that lived
    here, and the quicksort the rewriter used to produce — so there is no rewrite
    left to run and no second definition to keep in step.

    Everything this section asserted is asserted there, on the same program:

      * the headline (`progOk`), the RUN (`runQs` on seven inputs, against Lean's
        own sort), and the twin battery, which grew from three to six on the way.
      * `toP`'s own regression — that the rewrite really did change both call sites
        — was a `calleeNames` probe of a term-rewriter's output, and it retires with
        the rewriter rather than with a claim. The call sites are now written, not
        computed: `partition(f2, &mut *v, x, hfuel)` and `append_back(lv, &mut *v,
        w, LeRefl lv)` are lines of the source.

    What does NOT move is the DIFFERENTIAL, which is this file's own business and
    the one thing §F asserted that is about programs rather than about quicksort:
    the two machines agree on the whole final Ω of the largest program in the
    corpus. Kept below, on `S23Direct`'s chain. -/

/-- The two machines agree on the whole final Ω of the flagship — the differential
    of M26-C, run on a program rather than on a `FnDef` body, at the largest scale
    the corpus has. -/
example : progDiff (Tests.S23Direct.qsRun [3, 1, 2]) = true := by native_decide

/-! ## §G. The ARRAY flagship — RETIRED HERE (M28 D8), for the same reason as §F

    `quicksortA` is the array era's in-place scan: it carves, swaps through element
    borrows, and returns an index. It shares no code with §F's list quicksort — not
    the program, not the predicates, not the partition, not the container. This
    section assembled it from `S25ArrSort`'s three declarations with `progOf`,
    checked it against no table, ran it in place on real arrays, substituted each of
    seven lie twins into the cohort, and re-ran the cross-differential between the
    two sorts in program-term form.

    Every one of those is now asserted in `S25ArrSort` itself, on the same program:
    the flagship is one `fn` chain there (`arrUnder`), with the three return types
    and `quicksortA`'s sufficiency hypothesis as PARAMETERS — so the twin
    substitution this section implemented as `Sub` (replace the cohort member whose
    name matches) is a varied argument, and the cross-differential's two sides are
    two programs rather than two tables.

    **The finding this section recorded is the one to carry, and it is unchanged**:
    the array cohort was ALREADY fuel-threaded (`splitA [fuel]`, `quicksortA
    [fuel]`, `partitionA` not recursive at all), so §12 decision 8 costs this lane
    nothing. R12's carve machinery — the part of the corpus that leans hardest on
    the call boundary's re-mint — transferred to the seal without a single
    adjustment, which is the strongest available evidence that §5's opacity and
    §6.1's call rule really are the same mechanism reached two ways. -/

/-! ## §H. Both dispatch surfaces, for the rules this phase added

    The standing warning (M26-C §K, earned when phase B's fence was DEAD until
    duplicated at the driver): `explore` is a second dispatch surface, and a
    statement-position `match` or `let` never reaches `readR`'s own cases. Every
    rule here has to be exercised where `pushContinuations` sends a real body —
    INSIDE a branch of a symbolic match — and not only at the top level.

    The rules this phase added are `admitGlobals` (at `.lamR` and at the seal) and
    `endScope`. They are reached by construction rather than by duplication, and
    the reason is worth stating because "no duplication needed" is exactly what a
    phantom rule looks like from the inside: a runtime λ and a seal are always
    EXPRESSIONS — a let's right-hand side, an argument, a tail — and the driver
    reaches every expression through `.letIn`'s right-hand side, `.seq`'s
    expression, and the final-expression fall-through. `endScope` runs per path
    after the walk, so a forked path gets its own.

    Each is placed inside a branch with a NEGATIVE TWIN at the same position, so
    the branch is not merely skipped. -/

/-- A symbolic scrutinee at the top level of a program: an abstract call's result
    is a σ, and matching on one is what forks the driver's paths. -/
def hSplit (inZ inS : Term) : Term :=
  .letIn ⟨0, "F"⟩ (prog{ (λ (x : Nat). x : Π (x : Nat) → Nat) })
    (.letIn ⟨1, "n"⟩ (Term.appSpine (.var ⟨0, "F"⟩) [prog{ 3 }])
      (.matchE ⟨1, "n"⟩ none [Branch.mk "Z" [] inZ, Branch.mk "S" [⟨2, "k"⟩] inS]))

-- H0. The split is real: two paths, not one.
example : (programEnvs (hSplit .unit .unit)).length == 2 := by native_decide

-- H1. A GLOBAL-REFERENCING runtime λ, formed and called inside a branch. `f` is
-- the program-level binding two `let`s above; the branch is a body, so this is
-- `admitGlobals` reached through the driver.
def hGlobal (bad : Bool) : Term :=
  hSplit .unit
    (.letIn ⟨3, "G"⟩ (Term.lamTel [(⟨4, "y"⟩, .const "Nat")] (Term.appSpine (.var ⟨0, "F"⟩) [.var ⟨4, "y"⟩]))
      (.letIn ⟨5, "r"⟩ (Term.appSpine (.var ⟨3, "G"⟩) [.var ⟨2, "k"⟩])
        (if bad then prog{ True } else .unit)))
example : progOk (hGlobal false) = true := by native_decide
-- The negative twin at the SAME position: the branch is entered and its result
-- audited, so the accept above is not the branch being skipped.
example : progRejects (hGlobal true) "does not have return type" = true := by native_decide

-- H2. A CAPTURE inside a branch is refused there too — the fence is not weaker on
-- a path than at the top level. (`k` is the branch's own binder, a `Nat`, so this
-- is data capture: the same rejection §D2a pins, reached the other way.)
def hCapture : Term :=
  hSplit .unit
    (.letIn ⟨3, "G"⟩ (Term.lamTel [(⟨4, "y"⟩, .const "Nat")] (.letIn ⟨6, "z"⟩ (.var ⟨2, "k"⟩) (.var ⟨4, "y"⟩)))
      .unit)
example : progRejects hCapture "a runtime (lowercase) binding" = true := by native_decide

-- H3. A SEAL inside a branch fires its audit there, in that branch's Ω.
def hSeal (bad : Bool) : Term :=
  hSplit .unit
    (.letIn ⟨3, "Sf"⟩
      (.seal 0 (Term.lamTel [(⟨4, "y"⟩, .const "Nat")] (.var ⟨4, "y"⟩))
        (if bad then prog{ Π (y : Nat) → Bool } else prog{ Π (y : Nat) → Nat }))
      .unit)
example : progOk (hSeal false) = true := by native_decide
example : progRejects (hSeal true) "does not have return type (Bool)" = true := by native_decide

-- H4. `endScope` runs PER PATH. The borrow is lent inside ONE branch only, so the
-- path that lends must demand it back at its own end while the path that does not
-- has nothing to demand — and the differential is what says both are right, since
-- the concrete run takes exactly one of them.
def hLend : Term :=
  .letIn ⟨0, "Push"⟩
    (prog{ (λ(e : Nat, v : &mut (s : List Nat ~> List Nat)){
                  let tail = *v; *v := Cons(e, tail); () } : Π (e : Nat) → Π (v : &mut (s : List Nat ~> List Nat)) → Unit) })
    (.letIn ⟨1, "l"⟩ (prog{ Cons(1, Nil) })
      (.letIn ⟨2, "id"⟩ (prog{ (λ (x : Nat). x : Π (x : Nat) → Nat) })
        (.letIn ⟨3, "n"⟩ (Term.appSpine (.var ⟨2, "id"⟩) [prog{ 3 }])
          (.matchE ⟨3, "n"⟩ none
            [Branch.mk "Z" [] .unit,
             Branch.mk "S" [⟨4, "k"⟩]
               (.letIn ⟨5, "r"⟩ (Term.appSpine (.var ⟨0, "Push"⟩) [.var ⟨4, "k"⟩, .borrow (.var ⟨1, "l"⟩)])
                 .unit)]))))
example : progOk hLend = true := by native_decide
example : progDiff hLend = true := by native_decide
-- It really is two paths, and the lending one really does end its loan: no path
-- leaves `l` holding a parked loan.
example : ((programEnvs hLend).length == 2
        && (programEnvs hLend).all (fun r => match r with
             | .ok env => !((env.lookup "l").any (fun v => match v with
                 | .loanM _ => true | _ => false))
             | .error _ => false)) = true := by native_decide
-- …and the raw walk (no end-of-scope demand) leaves one, so the assertion above is
-- about `endScope` and not about the program never lending.
example : (rawEnvs hLend).any (fun r => match r with
    | .ok env => (env.lookup "l").any (fun v => match v with | .loanM _ => true | _ => false)
    | .error _ => false) = true := by native_decide

end Dllbc.Tests.S26Prog
end
-- └── end of what was `S26Prog.lean` ───────────────────────────────────────────────

-- ┌── M33b: the demand battery ──────────────────────────────────────────────────────
section
/-!
# §33 (M33b) — what a recursion LEAVES BEHIND

**DLLBC is an eager language** (user ruling, 2026-08-13): *"Passing a Nat to
natRec causes the Nat to get recursed over all the way to the end — this means it
will definitely call the zero case, passing it unit and evaluating the contents. I
don't see why we would want anything unevaluated leaving the natRec; this is not a
lazy language."*

It does not do that yet, and these programs are the measurement of the gap. Each
one asserts the behaviour of the tree as it is at this commit, which for two of the
three is behaviour nobody wants; **they flip DELIBERATELY at M33b commit 3**, which
says so in its message and edits the assertions in place rather than deleting them.

The subject is one function and its result is what everything turns on:

    fn Build [n] (n : Nat) -> List Nat {
      match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
    }

Its motive is DATA (a `List Nat`, not a function type) and its residual telescope
is EMPTY (the scrutinee is its only parameter). `fnElab` therefore gives the `Z`
arm no binders at all — a bare term where every other arm is a λ — and ι, having
nothing to apply it to, hands the arm back as the value. So `Build(1)` evaluates
to `Cons Z ⟨natRec … Z⟩`: a constructor with an unreduced recursor spine in its
tail, which is a STATE form (R1's `§rec`, the value with no `Term`) sitting where
the program wrote a list.

Nothing in the corpus had noticed, because no corpus program consumes a
data-motive recursion's result — every recursive `fn` here writes through a borrow
and returns `Unit`. These three do consume it, one per way there is to. -/

open Dllbc
open Dllbc.StdLemmas (Len)

namespace Dllbc.Tests.S33Eager

/-- The subject. Spelled once and spliced, so the three programs below differ in
    exactly what they do with the result. -/
def build : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  () }

/-! ## §A. Demand it with a runtime match — the executing machine gets STUCK

    The tail's match lives in its own `fn` for a reason that is not about this
    milestone: `pushContinuations` re-wraps an arm's body into `.seq body k`
    without re-normalizing, so a statement match NESTED in another match's arm
    lands back in expression position and the checker refuses it there ("only a
    statement-position match may split"). That is a pre-existing limit of the
    normalizer, it has nothing to do with eagerness, and spelling the inner match
    as a callee keeps this test about the thing it is about. -/

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

-- The checker accepts: to it `r`'s tail is an ordinary `σ : List Nat` and the
-- split is the ordinary symbolic one.
example : progOk demandMatch = true := by native_decide
-- **FLIPPED AT COMMIT 3.** It used to be `false` — the run died at "match: no
-- branch for constructor '§rec'", because the tail held an unreduced recursor
-- spine. `Build(1)` now evaluates to `Cons Z (Cons (S Z) Nil)` and the match on
-- the tail is an ordinary match on an ordinary list.
example : progRuns demandMatch = true := by native_decide

-- …and the recursion really did run all the way to the end, which is the
-- ruling's own sentence and what says the two lines above are not the match
-- being skipped. `Build(3)` is four `Cons` cells deep, the last of them the base
-- arm's `Cons(1, Nil)`.
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

/-! ## §B. Demand it as KNOWLEDGE — and this is the clean differential violation

    `let L = Len r` is a capital `let`, so its right-hand side is ⇝-read, and a ⇝
    read of a `§rec` spine is refused by name ("is state, not knowledge"). The two
    machines disagree about the SAME program with no rule to appeal to: one accepts
    it, the other cannot run it. That is the shape a differential exists to catch,
    and it is why this milestone is a kernel change and not a macro tidy-up. -/

def demandLen : Term := prog{
  fn Build [n] (n : Nat) -> List Nat {
    match n { Z => Cons(1, Nil), S(k) => Cons(0, Build(k)) }
  };
  let r = Build(1);
  let L = Len r;
  () }

example : progOk demandLen = true := by native_decide
-- **FLIPPED AT COMMIT 3, AND THIS IS THE HEADLINE.** It used to be `false`. The
-- pair was the assertion — neither line alone said anything, and together they
-- said the machines did not agree about a program with no rule to appeal to.
-- Now they agree, and the pair says THAT.
example : progRuns demandLen = true := by native_decide

/-! ## §C. Never demand it — and overwrite it through a borrow

    Before commit 3 this was laziness paying off: the tail was never forced, so
    writing over it cost nothing. **Its MEANING changed and its verdict did not**,
    which is what it was pinned for: the tail is a finished list now and this is an
    ordinary overwrite of one. -/

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

    A recursion is a function, so two calls of it are two values and writing
    through one must not be visible in the other. That property is now
    STRUCTURAL: the base arm is a λ, so its body is evaluated when ι selects it
    rather than when the spine is formed, and each call's cells are that call's.

    Honest about what this is and is not. The property held before M33b too, but
    it was carried by copy-on-read (R1's `§rec` finding: a recursor spine is
    index-kind, "found by executing-mode `m1` zeroing half a list"), and the base
    arm's one value was built once at spine formation and copied thereafter. Both
    mechanisms are live; what the pair below pins is the PROPERTY, so that a later
    change to either mechanism has to say so here. -/

/-- Mutate the cell the BASE ARM built. -/
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

/-- Mutate a cell the RECURSION built — the tail of `Build(1)`, which before M33b
    was the unreduced spine. **`r2`'s rendering is the new part**: it is a
    finished list where it would have read `Cons Z (natRec @motive …)`. -/
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

end Dllbc.Tests.S33Eager
end
-- └── end of M33b's demand battery ─────────────────────────────────────────────────
