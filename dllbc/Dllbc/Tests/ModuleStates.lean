import Dllbc.ElabCheck
import Dllbc.StdChain
import Dllbc.Std

/-! # Module states (docs/20 stages 1-3) — the surface

    `prog () { … }` and `prog (e) { … }` elaborate to a `Checked` — the term and
    the walk's ending state. Elaborating a module block IS its definition-site
    check, and a seeded block resolves names against the seed's Ω. These are the
    acceptance cases of docs/20; the manual seeding they replace is
    `Tests/ProbeModuleStates.lean` (the stage-0 probe, kept as the record of
    what was measured before the surface existed). -/

open Dllbc

namespace Dllbc.Tests.ModuleStates

-- `#guard_msgs` below pins error text exactly, so trace output must stay off.
set_option trace.Dllbc.check false

/-! ## (1) The std module: checked at its own elaboration

    This block elaborating at all is the assertion: a `fn` whose body did not
    inhabit its signature would be a red squiggle here, not a latent value. -/

def std : Checked := prog () {
  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };
  () }

/-! ## (2) A seeded consumer: `LeRefl` resolves against the seed -/

def use1 : Checked := prog (std.env) {
  let y = LeRefl(2);
  () }

/-- The opaque call bound `y` to the fresh existential σ4, and the σ supply
    continued past the seed's rather than restarting. -/
example :
    ((use1.env.env.find? (fun kv => kv.1.name == "y")).map (fun kv => kv.2.pretty.startsWith "σ")
        == some true)
    && use1.env.nextSym == std.env.nextSym + 1 := by native_decide

/-! ## (3) Splice agreement: seeding means prefix-splicing -/

def spliced : Term := prog_parse {
  fn LeRefl [n] (n : Nat) -> Le n n {
    match n { Z => unit, S(k) => LeRefl(k) } };
  let y = LeRefl(2);
  () }

/-- The ONE block holding both pieces ends with the same `y` and the same
    `nextSym` as the seeded pair — docs/20's prefix-splice semantics, asserted
    on the projections that observe it. -/
example :
    (moduleFinalSt initSt spliced).toOption.map (fun s =>
        ((s.env.find? (fun kv => kv.1.name == "y")).map (fun kv => kv.2.pretty),
         s.nextSym))
      == some
        ((use1.env.env.find? (fun kv => kv.1.name == "y")).map (fun kv => kv.2.pretty),
         use1.env.nextSym) := by native_decide

/-! ## (4) Seal sites stay separate across the boundary

    Each block holds one sealed binding (a `fn` IS one). Without the site
    offset (`St.nextSite`) both seals would number 0, the consumer's ⇝-read
    would hit the seed's `sealSites` entry at the same captured inputs, and B
    would silently REUSE A's σ. The consumer elaborating green is half the
    assertion; distinct sites and distinct σs are the other half. -/

def sealMod : Checked := prog () {
  fn A () -> Nat { 2 };
  () }

def sealUse : Checked := prog (sealMod.env) {
  fn B () -> Nat { 3 };
  () }

example :
    sealUse.env.sealSites.length == 2
    && (sealUse.env.sealSites.map (·.1.1)).eraseDups.length == 2
    && (sealUse.env.sealSites.map (·.2)).eraseDups.length == 2 := by native_decide

/-! ## (5) Misusing an imported lemma is an elaboration error

    `LeRefl` takes a `Nat`; the call passes a `Bool`. The rejection surfaces as
    a diagnostic at elaboration, like any `prog{ }` rejection. -/

/--
error: dllbc:
call: argument (True) does not have its parameter type (Nat)
-/
#guard_msgs in
#check (prog (std.env) {
  let y = LeRefl(True);
  () } : Checked)

/-! ## (6) A chain: std → std2 → a consumer citing both

    `std2`'s lemma cites the IMPORTED `LeRefl` from inside its own `fn` body —
    the citation is captured from the seed's Ω exactly as a local sibling's
    would be — and the final consumer calls both lemmas of the chain. -/

def std2 : Checked := prog (std.env) {
  fn LeReflS (n : Nat) -> Le n n { LeRefl(n) };
  () }

def useBoth : Checked := prog (std2.env) {
  let p = LeRefl(1);
  let q = LeReflS(2);
  () }

example :
    (useBoth.env.env.find? (fun kv => kv.1.name == "p")).isSome
    && (useBoth.env.env.find? (fun kv => kv.1.name == "q")).isSome
    && useBoth.env.nextSym > std2.env.nextSym
    && std2.env.nextSym > std.env.nextSym := by native_decide

/-! ## (7) The `[k]` hint crosses the boundary (stage 3)

    `Walk`'s decreasing parameter is SECOND — the `TwoRec` / `Nth` shape
    (`Tests/Direct.lean`, `Tests/Boundaries.lean`), where `fnElab` hoists `n`
    to the front of the sealed telescope. Through stage 2 the seeded call
    below was UNCALLABLE: the hint lived only in the macro layer, so the
    imported call was built unpermuted and `&m xs` landed on the hoisted `Nat`
    parameter — an argument-type rejection. The hint now persists in the
    module's state (`Ledgers.hints`) and `moduleBinds` reads it back, so the
    consumer calls in DECLARATION order and gets the same permutation a local
    call gets. -/

def walkMod : Checked := prog () {
  fn Walk [n] (v : &mut List Nat, n : Nat) -> Unit {
    match n { Z => (), S(k) => Walk(&m *v, k) } };
  () }

def useWalk : Checked := prog (walkMod.env) {
  let xs = Cons(1, Nil);
  let r = Walk(&m xs, 2);
  () }

/-- The permuted call checked: `r` is bound to the call's fresh existential and
    the σ supply continued past the seed's. The elaboration going green is the
    other half — types make an unpermuted call impossible here, since it would
    pass a borrow where the hoisted telescope wants a `Nat`. -/
example :
    ((useWalk.env.env.find? (fun kv => kv.1.name == "r")).map (fun kv => kv.2.pretty.startsWith "σ")
        == some true)
    && useWalk.env.nextSym > walkMod.env.nextSym := by native_decide

/-- The persisted hint channel holds the declaration-order index of `Walk`'s
    scrutinee — and nothing else, since only hinted `fn`s get entries. -/
example : walkMod.env.ledgers.hints == [("Walk", 1)] := by native_decide

/-- The channel survives the chain: `std2`'s walk audits `LeReflS`'s seal with
    the seed's entries in hand, and they come back out (`Ledgers.closePath`).
    `LeRefl`'s hint is index 0 — a no-op permutation, but a real entry — and
    `LeReflS`, unhinted, adds none. -/
example :
    std.env.ledgers.hints == [("LeRefl", 0)]
    && std2.env.ledgers.hints == [("LeRefl", 0)]
    && useWalk.env.ledgers.hints == [("Walk", 1)] := by native_decide

/-! ## (8) The span channel: statement spans persist as plain data

    The `SpanAcc` join table the defining elaboration used to discard: each
    statement's term key, with the defining MODULE's name and byte offsets.
    Positions are file-content-dependent, so the assertions pin the invariants
    — non-empty, the right module, well-formed extents, growth along a chain —
    not the offsets themselves. -/

example :
    walkMod.env.ledgers.spans.length > 0
    && walkMod.env.ledgers.spans.all (fun s =>
         s.module == "Dllbc.Tests.ModuleStates" && s.start < s.stop)
    -- The seeded block's channel extends the seed's: its own statements join
    -- the imported ones rather than replacing them.
    && useWalk.env.ledgers.spans.length > walkMod.env.ledgers.spans.length
    := by native_decide

/-- The hover-replay channels stay pinned off in a persisted state — stage 3
    keeps `moduleFinalSt`'s equality story honest by rebuilding the ledgers
    with ONLY the module-boundary channels (the seal audit would otherwise
    leave `[] :: …` residue in `paths` even with the flags off). -/
example :
    walkMod.env.ledgers.letTypes.isEmpty
    && walkMod.env.ledgers.points.isEmpty
    && walkMod.env.ledgers.paths.isEmpty
    && useWalk.env.ledgers.paths.isEmpty := by native_decide

/-! ## (7) The real standard library, consumed

    `Dllbc.std` is the 110-lemma chain (StdChain.lean). Seeding from its state
    and citing lemmas by name — including feeding one imported lemma's result
    to another — is the design's whole payoff, exercised on the real library
    rather than this file's toy module. -/

def useStd : Checked := prog (Dllbc.std.env) {
  let p = LeRefl(3);
  let w = LeUpR(3, 3, p);
  let u = AddComm(2, 3);
  () }

example :
    (useStd.env.env.find? (fun kv => kv.1.name == "p")).isSome
    && (useStd.env.env.find? (fun kv => kv.1.name == "w")).isSome
    && (useStd.env.env.find? (fun kv => kv.1.name == "u")).isSome
    && useStd.env.nextSym > Dllbc.std.env.nextSym := by native_decide


/-! ## (8) Seeded test helpers — the golden-and-mutants pattern

    A golden program is a checked `prog (seed) { … }`; its mutants are Terms
    (built by `prog_parse` or by editing `golden.term`) checked from the SAME
    seed by `progRejectsFrom`/`progOkFrom`. The fragment below is unseeded at
    elaboration: its `LeRefl(True)` is an unresolved `.call` that the helper
    retargets at the seed's declarations before walking. -/

def mutantArg : Term := prog_parse { let y = LeRefl(True); () }
example : progRejectsFrom Dllbc.std.env mutantArg "does not have its parameter type" = true := by
  native_decide

def goldenTerm : Term := prog_parse { let y = LeRefl(2); () }
example : progOkFrom Dllbc.std.env goldenTerm = true := by native_decide

-- A mutant made from a CHECKED golden's own term (already retargeted): the
-- helper's retarget is a no-op on it and the walk still runs from the seed.
example : progOkFrom Dllbc.std.env use1.term = true := by native_decide

/-- Executing from the seed: the program's own bindings, the seed's dropped.
    Known limitation (docs/20): the seed was interpreted in checking mode, so a
    library fn called under `executing := true` is not entered — `y` is an
    existential here, not a concrete proof value. A library interpreted in
    executing mode would be needed for concrete proof values to flow. -/
example : (runProgramFrom Dllbc.std.env goldenTerm).isOk = true := by native_decide

end Dllbc.Tests.ModuleStates
