import Dllbc.ElabCheck
import Dllbc.Std

/-! # Module states (docs/20 stages 1-2) — the surface

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
    ((use1.env.env.find? (fun kv => kv.1.name == "y")).map (fun kv => kv.2.pretty)
        == some "σ4")
    && use1.env.nextSym == std.env.nextSym + 1 := by native_decide

/-! ## (3) Splice agreement: seeding means prefix-splicing -/

def spliced : Term := prog defer_check {
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

end Dllbc.Tests.ModuleStates
