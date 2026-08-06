import Dllbc.Program
import Dllbc.Std
import Dllbc.StdLemmas
import Dllbc.PureMacro
import Dllbc.ProgMacro
import Dllbc.Tests.S26Seal

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
change at all. A *pure* binder is de Bruijn and has no name, so its mode rides
on the domain: `Π (X : τ) → …` is `.pi (.cmpT τ) …`. `Term.cmpT`/`Val.cmpT` is
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
open Dllbc.StdLemmas (le_refl le_trans)
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
-- because a `%`-spliced tail may not declare functions (both chains would number
-- their slots from `progBase` and the inner would shadow the outer), so the
-- callee line is repeated rather than factored.

-- A1. THE PAIN. The proof is passed, and citing it afterwards is a use-after-move.
def a1 : Term := prog{
  fn useLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { useLe(n, m, hnm); hnm };
  () }
example : progRejects a1 "holds ⊥" = true := by native_decide

-- A2. THE FIX. The same program against the capital twin: accepted, because the
-- argument was ⇝-read and never left the caller's slot.
def a2 : Term := prog{
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { useLeC(n, m, hnm); hnm };
  () }
example : progOk a2 = true := by native_decide

-- A3. …and it is not a one-shot: passed twice, cited after both.
def a3 : Term := prog{
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { useLeC(n, m, hnm); useLeC(n, m, hnm); hnm };
  () }
example : progOk a3 = true := by native_decide

-- A4. The staging that R16 forced, and what it becomes. `mkHf`'s shape — capture
-- a proof into a λ *before* the call that consumes it — still works, and is now
-- unnecessary: A3 is the same program without it.
def a4 : Term := prog{
  fn useLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let mk = λ (u : Unit). hnm; useLe(n, m, hnm); mk unit };
  () }
example : progOk a4 = true := by native_decide

/-! ### A5. `match fuel` against its capital twin

    The flagship's two halves, isolated: a lowercase binder is branched on, and
    the capital twin — same type, same position — cannot be. This is the pair
    that says the modes are doing work rather than decorating. -/

def a5lo : Term := prog{ fn a5lo (fuel : Nat) -> Unit { match fuel { Z => (), S(f2) => () } }; () }
def a5hi : Term := prog{ fn a5hi (Fuel : Nat) -> Unit { match Fuel { Z => (), S(f2) => () } }; () }
example : progOk a5lo = true := by native_decide
example : progRejects a5hi "cannot be the scrutinee of a runtime match" = true := by native_decide

-- A6. A comptime argument must be a COMPTIME term. A call's result is a fresh
-- existential with no ⇝ reading, so it cannot be spliced into a capital position
-- directly — it must be `let`-bound first. An honest rejection rather than a
-- silent fall-back to ⇒, and the `let`-bound form immediately above works.
def a6bad : Term := prog{
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn giveLe (a : Nat) -> Le a a { %le_refl a };
  fn caller (n : Nat) -> Unit { useLeC(n, n, giveLe(n)); () };
  () }
def a6ok : Term := prog{
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn giveLe (a : Nat) -> Le a a { %le_refl a };
  fn caller (n : Nat) -> Unit
  { let p = giveLe(n); useLeC(n, n, p); useLeC(n, n, p); () };
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
def b1hi : Term := prog{ fn b1 (N : Nat) -> Unit { let y = N; () }; () }
def b1lo : Term := prog{ fn b1 (n : Nat) -> Unit { let y = n; () }; () }
example : progRejects b1hi "cannot be ⇒-moved" = true := by native_decide
example : progOk b1lo = true := by native_decide

-- B2. The runtime match — §A5 above, which is where it earns its keep.

-- B3. The borrow.
def b3hi : Term := prog{ fn b3 (N : List Nat) -> Unit { let b = &mut N; () }; () }
def b3lo : Term := prog{ fn b3 (n : List Nat) -> Unit { let b = &mut n; () }; () }
example : progRejects b3hi "cannot be borrowed" = true := by native_decide
example : progOk b3lo = true := by native_decide

-- B4. The write-through (⇐).
def b4hi : Term := prog{ fn b4 (N : Nat) -> Unit { N := 3; () }; () }
def b4lo : Term := prog{ fn b4 (n : Nat) -> Unit { n := 3; () }; () }
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
def b5hi : Term := prog{ fn b5 (N : Nat) -> Unit { %b5body }; () }
example : progRejects b5hi "cannot be indexed or sliced" = true := by native_decide

-- B6. A capital binder handed to a LOWERCASE parameter. Same rejection as B1
-- and a different demand site — `processArgs` reads a runtime parameter's
-- argument with ⇒, so the fence fires there. This is the direction that makes
-- the fence coherent: a comptime binder cannot launder itself into runtime by
-- being passed to something that wants a runtime value.
def b6 : Term := prog{
  fn useLe (a : Nat, b : Nat, h : Le a b) -> Unit { () };
  fn caller (n : Nat, m : Nat, Hnm : Le n m) -> Unit
  { useLe(n, m, Hnm); () };
  () }
example : progRejects b6 "cannot be ⇒-moved" = true := by native_decide

/-! ### B7. §6.3's distinction, mechanical: `map_spec (G : …)` vs `map_apply (g : …)`

    The one place where kind cannot decide the mode. A capital function-typed
    binder is a SPEC parameter — the caller may supply an abstract or sealed
    function with no runtime existence — so the body may cite `G a` in a type,
    where ⇝ gives the structured neutral, but may not CALL it. The lowercase twin
    is `S26Seal`'s `apply1`, and calling it is exactly what the lowercase buys. -/

def b7spec : Term := prog{
  fn b7spec (G : Π (x : Nat) → Nat, n : Nat) -> Unit { let r = G(n); () };
  () }
example : progRejects b7spec "cannot be CALLED under ⇒" = true := by native_decide
example : progOk S26Seal.apply1 = true := by native_decide

-- …and the citation that IS allowed: `G a` in a type position, where the whole
-- content is §2.1's structured neutral. `G` is never supplied at runtime.
def b7cite : Term := prog{
  fn b7cite (G : Π (x : Nat) → Nat, n : Nat) -> Id Nat (G n) (G n) { Refl };
  () }
example : progOk b7cite = true := by native_decide

/-! ### B8/B9. Borrow-typed binders must be lowercase — checked, not assumed

    §6 states this as a requirement on the design; it is checked at BOTH ends,
    and the two rejections are distinguishable so the site is pinned rather than
    inferred. The declaration is caught by `seedTelescope` (the honest place: the
    signature is wrong); the call site is caught by `processArgs`, which matters
    for a table entry that was never itself checked. -/

def b8 : Term := prog{ fn b8 (V : &mut List Nat) -> Unit { () }; () }
example : progRejects b8 "telescope: parameter 'V' is capitalized" = true := by native_decide

def b9 : Term := prog{
  fn b8 (V : &mut List Nat) -> Unit { () };
  fn caller () -> Unit { let x = Cons(1, Nil); b8(&mut x); () };
  () }
-- The needle is NAME-FREE since M27-δ, and the reason belongs beside it: `fsig`
-- stores the ascribed Π itself now, and a Π has no binder names — `piBinderNames`
-- synthesizes `A0`/`a0` at the call, encoding the MODE (which is what the rule
-- needs) and losing the display name (which is what the message had). A
-- synthesized name is as unstable as a σ id, so pinning one would rot.
example : progRejects b9 "is capitalized" = true := by native_decide

-- The lowercase twin of both, for liveness.
def b8lo : Term := prog{ fn b8lo (v : &mut List Nat) -> Unit { () }; () }
def b9lo : Term := prog{
  fn b8lo (v : &mut List Nat) -> Unit { () };
  fn caller () -> Unit { let x = Cons(1, Nil); b8lo(&mut x); () };
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

example : DeclMacro.reservedBinder "Cons" = true := by native_decide
example : DeclMacro.reservedBinder "Nat" = true := by native_decide
-- Lowercase names are NOT reserved: they were always shadowable, shadowing them
-- is ordinary scoping, and reserving `j`/`k` would cost every program its loop
-- indices for no disambiguation at all (`insert_at`'s own `k` parameter).
example : DeclMacro.reservedBinder "k" = false := by native_decide
example : DeclMacro.reservedBinder "unit" = false := by native_decide
example : DeclMacro.reservedBinder "Hfuel" = false := by native_decide

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
  fn c1 (v : &mut List Nat) -> Id (List Nat) (*v) (old *v) { let L = *v; Refl };
  () }
def c1bad : Term := prog{
  fn c1bad (v : &mut List Nat) -> Id (List Nat) (*v) (old *v) { let l = *v; Refl };
  () }
example : progOk c1 = true := by native_decide
-- The runtime take leaves a hole in the borrow, and a hole satisfies no type
-- (§5.4). Same program, one character — and the rejection names the hole, so
-- this is the take-vs-projection difference and not some other breakage.
example : progRejects c1bad "holds a hole (⊥) at return" = true := by native_decide

-- C2. The fence applies to a capital `let` exactly as to a capital parameter —
-- so the snapshot above is a SPECIFICATION binding, not a free copy of the data.
def c2 : Term := prog{ fn c2 (v : &mut List Nat) -> Unit { let L = *v; let y = L; () }; () }
example : progRejects c2 "cannot be ⇒-moved" = true := by native_decide

-- C3. The right-hand side must have a ⇝ reading. A call's result is a fresh
-- existential and has none, so a capital `let` cannot bind one — honest, and
-- pointing at the lowercase `let` that can.
def c3bad : Term := prog{
  fn giveLe (a : Nat) -> Le a a { %le_refl a };
  fn caller (n : Nat) -> Unit { let P = giveLe(n); () };
  () }
example : progRejects c3bad "not in the comptime fragment" = true := by native_decide

-- C4. Locally-derived certificates without staging: a capital `let` builds the
-- certificate, and citing it at capital argument positions never consumes it.
def c4 : Term := prog{
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let Q = le_trans n m m hnm (%le_refl m);
    useLeC(n, m, Q); useLeC(n, m, Q); hnm };
  () }
example : progOk c4 = true := by native_decide

/-! ## §D. Erased data — the capability kind-derivation cannot express

    A capital `N : Nat` used only in types is QTT's quantity 0. The point is
    sharp precisely because `Nat` is already index-kind: §2.1's copy-on-read
    heuristic classifies it as copyable, and copy-on-read is *not* erasure — a
    copyable binder can still be branched on. The mode is what forbids that, and
    kind cannot derive it, because the two binders below have the same kind. -/

-- Accepted: `N` appears only in the return TYPE.
def d1 : Term := prog{ fn d1 (N : Nat) -> Id Nat N N { Refl }; () }
example : progOk d1 = true := by native_decide

-- Accepted: an erased length index, with the runtime data typed against it.
def d2 : Term := prog{
  fn d2 (N : Nat, l : List Nat, h : Id Nat (len l) N) -> Id Nat (len l) N { h };
  () }
example : progOk d2 = true := by native_decide

-- Fenced: the body tries to branch on it. Same type, same kind, same position as
-- §A5's `fuel` — only the case differs, and only the case can decide this.
def d3 : Term := prog{ fn d3 (N : Nat) -> Unit { match N { Z => (), S(k) => () } }; () }
example : progRejects d3 "cannot be the scrutinee of a runtime match" = true := by native_decide

/-! ## §E. Case is inert under ⇝ — pinned from both sides

    §6's heading, as two assertions that together say the modes are exactly as
    strong as intended and no stronger: the two Π's are the same type to every
    comptime judgment, and ⇒ still tells them apart. -/

-- E1. The mode is invisible to conversion…
example : Val.convert 1000 (.pi (.cmpT (.const "Nat")) (.const "Nat"))
                           (.pi (.const "Nat") (.const "Nat")) = true := by native_decide
-- …and NOT erased by normalization, which is what leaves ⇒ something to read.
-- (`==` is mode-blind, so this has to be asked structurally.)
example : (match Val.nfV 1000 (Val.pi (.cmpT (.const "Nat")) (.const "Nat")) with
           | .pi d _ => Val.domComptime d
           | _ => false) = true := by native_decide

-- E2. `add` stays all-lowercase and is cited in a spec regardless — you never
-- capitalize a definition to use it in a type. Both cases of the CITING
-- function's own binders work, because the citation happens under ⇝.
def e2lo : Term := prog{ fn e2lo (a : Nat, b : Nat) -> Id Nat (add a b) (add a b) { Refl }; () }
def e2hi : Term := prog{ fn e2hi (A : Nat, B : Nat) -> Id Nat (add A B) (add A B) { Refl }; () }
example : progOk e2lo = true := by native_decide
example : progOk e2hi = true := by native_decide

-- E3. The structured neutral — §2.1's `id_congr` mechanism — is unchanged by the
-- Π's binder case. An abstract function applied twice in a type position is ONE
-- term either way, which is what `Refl` inhabiting the `Id` says.
def e3lo : Term := prog{ fn e3lo (f : Π (x : Nat) → Nat, a : Nat) -> Id Nat (f a) (f a) { Refl }; () }
def e3hi : Term := prog{ fn e3hi (f : Π (X : Nat) → Nat, a : Nat) -> Id Nat (f a) (f a) { Refl }; () }
example : progOk e3lo = true := by native_decide
example : progOk e3hi = true := by native_decide

/-! ### E4. The two equalities are asymmetric, deliberately

    `Val.beq` is mode-blind because `convert` is built on it and §6 says case is
    inert under ⇝. `Term.beq` is STRUCTURAL, because its clients are not
    conversions: §18's `absOcc` abstracts occurrences by it (a mode-blind version
    would match `⇝τ` against `τ` and abstract the marker away with the domain),
    and `FnDef.alphaEq` is the macro-vs-corpus round-trip criterion — a mode-blind
    version would let phase D's `fn` macro emit a differently-moded `FnDef` and
    still report equivalence. Pinned because "one of these two is mode-blind and
    the other is not" is exactly the kind of asymmetry a later reader would
    otherwise assume was an oversight. -/

example : ((Val.cmpT (.const "Nat") : Val) == Val.const "Nat") = true := by native_decide
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
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let g = seal(λ (H : Le n m). Z, Π (H : Le n m) → Nat);
    let r = g(hnm);
    let s = g(hnm);
    hnm };
  () }
example : progOk f1 = true := by native_decide

-- F2. The lowercase twin of the same seal: the call MOVES the proof.
def f2 : Term := prog{
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let g = seal(λ (h : Le n m). Z, Π (h : Le n m) → Nat);
    let r = g(hnm);
    hnm };
  () }
example : progRejects f2 "holds ⊥" = true := by native_decide

-- F3. THE ASCRIPTION IS THE CONTRACT. The same lowercase-bindered λ, sealed at a
-- CAPITAL-bindered Π: accepted (conversion is mode-blind), and the call takes
-- its argument by ⇝, because the caller's view is the Π and nothing else.
def f3 : Term := prog{
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let g = seal(λ (h : Le n m). Z, Π (H : Le n m) → Nat);
    let r = g(hnm);
    let s = g(hnm);
    hnm };
  () }
example : progOk f3 = true := by native_decide

-- F4. The transparent case: a literal λ callee carries its modes on its own
-- domains, so the same routing happens with no seal in sight.
def f4 : Term := prog{
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let g = λ (H : Le n m). Z; let r = g(hnm); let s = g(hnm); hnm };
  () }
example : progOk f4 = true := by native_decide

-- F5. …and its lowercase twin moves, which is what says F4 is about the mode.
def f5 : Term := prog{
  fn caller (n : Nat, m : Nat, hnm : Le n m) -> Le n m
  { let g = λ (h : Le n m). Z; let r = g(hnm); let s = g(hnm); hnm };
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

def g1 : Term := prog{ let f = λ (x : Nat). λ (y : Nat). x; let z = f(2); () }
example : progRejects g1 "partial application" = true := by native_decide
example : progRejects g1 "binder modes do NOT separate the two cases" = true := by native_decide

-- The legitimate-return case, pinned as the LIMITATION it is: `mk` means to be
-- "the constant function at 1", and is refused.
def g2 : Term := prog{
  let mk = seal(λ (x : Nat). λ (y : Nat). x, Π (x : Nat) → Π (y : Nat) → Nat);
  let k1 = mk(1); () }
example : progRejects g2 "partial application" = true := by native_decide

-- Modes ARE expressible on such a Π — the elaboration is fine, the marker is
-- there — and change nothing, which is the point.
def g3 : Term := prog{
  let mk = seal(λ (X : Nat). λ (y : Nat). X, Π (X : Nat) → Π (y : Nat) → Nat);
  let k1 = mk(1); () }
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

/-- KEPT AS A DECLARATION, and consumed as a VALUE rather than run: `S26Fn` §A's
    `roundTrips` battery holds it against `telePi`/`piPeel`, and it is the battery's
    only member with a CAPITAL binder — so it is the one that says the round trip
    preserves the mode marker and not merely the binder count. A `FnDef` a property
    is proved ABOUT is not a program, so this stays while the cohorts below declare
    their own `step` in their chains. -/
def step : FnDef := decl{ fn step (v : &mut List Nat, b : Nat, H : Le (len *v) b) -> Unit { () } }

def qsish : Term := prog{
  fn step (v : &mut List Nat, b : Nat, H : Le (len *v) b) -> Unit { () };
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn qsish [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (len *v) fuel) -> Unit
    { match fuel {
        Z => (),
        S(f2) => {
          step(&mut *v, S(f2), Hfuel);                       -- passed to a call…
          let Q = le_trans (len (old *v)) (S f2) (S f2) Hfuel (le_refl (S f2));
                                                              -- …and cited AFTERWARDS
          useLeC(len (old *v), S(f2), Q);                     -- the derived certificate, used
          () } } };
  () }
example : progOk qsish = true := by native_decide

-- H2. THE CALLEE'S DECLARATION IS WHAT DECIDES. The same body against `stepLo`,
-- whose proof parameter is lowercase: the call would move an erased binder, and
-- the fence says so. Which is the right division of labour — a caller cannot
-- know whether a callee needs its proof at runtime, so the callee declares it.
def qsishLo : Term := prog{
  fn stepLo (v : &mut List Nat, b : Nat, h : Le (len *v) b) -> Unit { () };
  fn useLeC (a : Nat, b : Nat, H : Le a b) -> Unit { () };
  fn qsishLo [fuel] (fuel : Nat, v : &mut List Nat, Hfuel : Le (len *v) fuel) -> Unit
    { match fuel {
        Z => (),
        S(f2) => {
          stepLo(&mut *v, S(f2), Hfuel);
          let Q = le_trans (len (old *v)) (S f2) (S f2) Hfuel (le_refl (S f2));
          useLeC(len (old *v), S(f2), Q);
          () } } };
  () }
example : progRejects qsishLo "cannot be ⇒-moved" = true := by native_decide

-- H3. …and `Hfuel`'s neighbour cannot be scrutinized, which is the other half of
-- §6's sentence: an erased index is erased, not merely copyable.
def qsishBad : Term := prog{
  fn qsishBad (v : &mut List Nat, N : Nat, HN : Id Nat (len *v) N) -> Unit
    { match N { Z => (), S(k) => () } };
  () }
example : progRejects qsishBad "cannot be the scrutinee of a runtime match" = true := by native_decide

-- H4. The exit/`old` machinery, unchanged by the presence of erased binders: an
-- erased length index, an erased proof about it, a comptime snapshot binding,
-- and a borrow, under a return type relating exit to entry.
def qsish2 : Term := prog{
  fn qsish2 (v : &mut List Nat, N : Nat, HN : Id Nat (len *v) N)
    -> Id (List Nat) (*v) (old *v)
    { let L = *v; Refl };
  () }
example : progOk qsish2 = true := by native_decide

/-! ### H5. What modes do NOT fix, pinned so it is not mistaken for one

    A bound stated about `*v` is invalidated by any call through `v`: the call
    re-mints the payload, so the second `step(&mut *v, …, Hfuel)` wants
    `Le (len σ') …` where `Hfuel` says `Le (len σ_entry) …`. That is M23's
    opacity working exactly as designed (§2.2 — "the forgetting is wanted"), and
    it is why the real `quicksort` derives a fresh bound per recursive call
    rather than reusing one.

    The pair below is the evidence that this is NOT a mode problem: capital and
    lowercase proof binders are refused *identically*, with the same message
    about the same parameter type. Modes resolve R16 (consumption); they do not
    touch R12 (staleness), and nothing in §6 claims otherwise. -/

def h5hi : Term := prog{
  fn step (v : &mut List Nat, b : Nat, H : Le (len *v) b) -> Unit { () };
  fn h5hi (v : &mut List Nat, f : Nat, Hf : Le (len *v) f) -> Unit
  { step(&mut *v, f, Hf); step(&mut *v, f, Hf); () };
  () }
def h5lo : Term := prog{
  fn step (v : &mut List Nat, b : Nat, H : Le (len *v) b) -> Unit { () };
  fn h5lo (v : &mut List Nat, f : Nat, hf : Le (len *v) f) -> Unit
  { step(&mut *v, f, hf); step(&mut *v, f, hf); () };
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
  fn step (v : &mut List Nat, b : Nat, H : Le (len *v) b) -> Unit { () };
  fn h6hi (v : &mut List Nat, f : Nat, Hf : Le (len *v) f) -> Le (len (old *v)) f
  { step(&mut *v, f, Hf); Hf };
  () }
def h6lo : Term := prog{
  fn step (v : &mut List Nat, b : Nat, H : Le (len *v) b) -> Unit { () };
  fn h6lo (v : &mut List Nat, f : Nat, hf : Le (len *v) f) -> Le (len (old *v)) f
  { step(&mut *v, f, hf); hf };
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

/-- `giveL` is the ONE declaration in this file that stays a `FnDef`, and the
    reason is the EXECUTING machine rather than the checker. §I's differential runs
    each shape concretely, and a nullary `fn` lowers to a runtime λ binding nothing
    — which `λr` refuses ("a thunk makes ι ambiguous"). So a program that DECLARES
    a nullary function checks (the seal mints a σ) but cannot be run, and I2's
    concrete side would fail before the relation was consulted. Kept as a table
    entry, which is what `progOk`/`diffC`'s `table` parameter is for: J1's bridge,
    documented in `Program.lean` as exactly this. The arity-1 callees below need no
    such treatment and are declared in their programs. -/
def giveL : FnDef := decl{ fn giveL () -> List Nat { Cons(1, Nil) } }

-- I1. Concrete: the capital call does not consume, so the list is still there.
def i1 : Term := prog{
  fn takeLC (L : List Nat) -> Unit { () };
  let a = Cons(1, Nil); takeLC(a); let b = a; () }
def i1lo : Term := prog{
  fn takeL (l : List Nat) -> Unit { () };
  let a = Cons(1, Nil); takeL(a); let b = a; () }
example : progOk i1 = true := by native_decide
example : progRejects i1lo "holds ⊥" = true := by native_decide
-- …and the environment says so directly: `a` survived the call and was moved by
-- the `let b = a` that follows it. `tailEnv` drops the program's own function
-- bindings, so the expected Ω is the one this assertion always had.
example : tailEnv i1 [("a", .bot), ("b", Val.cons (Val.nat 1) Val.nil)] = true := by
  native_decide

-- I2. Symbolic: the argument is a call's fresh existential rather than a literal.
def i2 : Term := prog{
  fn takeLC (L : List Nat) -> Unit { () };
  let a = giveL(); takeLC(a); let b = a; () }
example : progOk i2 (.const "Unit") [giveL] = true := by native_decide

-- I3. Through a VALUE callee, transparent and sealed.
def i3 : Term := prog{
  let a = Cons(1, Nil); let g = λ (L : List Nat). Z; let r = g(a); let b = a; () }
def i3s : Term := prog{
  let a = Cons(1, Nil); let g = seal(λ (L : List Nat). Z, Π (L : List Nat) → Nat);
  let r = g(a); let b = a; () }
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
def shapes : List (List FnDef × Term) :=
  [ ([], i1), ([giveL], i2), ([], i3), ([], i3s) ]
example : shapes.all (fun p => diffC p.1 p.2) = true := by native_decide

end Dllbc.Tests.S26Modes
