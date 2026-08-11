import Dllbc.Machine
import Dllbc.Uni
import Dllbc.ProgMacro
import Dllbc.Program
import Dllbc.StdLemmas

/-!
# M32 Stage V — the viability probe (suspensions.md §5)

Throwaway scaffolding for three bets. NOT a migration: it produces verdicts.

  * Bet (b) — readback-to-`Term` with `§`-σ-names. Its core is
    `Dllbc/StageVCore.lean` (below `Machine`, so `generalizeStuck`'s sweep can be
    routed through it — the canary); the checks here are the namespace
    disjointness claim and the three `alphaEq` comparison sites.
  * Bet (c) — raw closures at rest with conversion-on-demand: the three
    sub-questions of §5, including the deliberate reproduction of §3's
    non-commuting hazard.

Bet (a) — newest-wins name-keyed Ω — cannot be probed additively (it is a change
to `lookupSlot`/`bindSlot`/`setSlot`), so it lives on its own commit.
-/

namespace Dllbc.StageV

open Dllbc

/-! ## Bet (b) check 1 — the σ namespace is disjoint from every minted binder -/

/-- Every reserved binder name the kernel can mint, at sample indices. -/
def mintedBinders : List String :=
  (List.range 4).map readbackName ++ [genName, Surface.unusedSnapName]
    ++ (List.range 4).map Val.letName
    ++ (List.range 4).map (fun i => FnMacro.paramName ⟨i, "x"⟩)
    ++ ["§k", "§ih", "§h", "§t", "§x", "§y", "§n", "§xs", "§lo"]

/-- **suspensions.md §6's first sharp edge, measured.** No name the kernel binds
    is a σ-name, so `Term.substP`'s rebinding guard can never fire for one. -/
def sigmaNamesDisjoint : Bool :=
  mintedBinders.all (fun b => (symOfName? b).isNone)
    && (List.range 64).all (fun i => symOfName? (symName i) == some i)

/-- The guard's vacuity stated as the behaviour it implies rather than as the
    name comparison: substituting a σ-name under a binder of every minted shape
    reaches the occurrence in the body. -/
def substPReachesUnderMintedBinders : Bool :=
  mintedBinders.all (fun b =>
    let body : Term := .lam b .type (.pvar (symName 7))
    Term.beq (Term.substP (symName 7) (.const "Nat") body) (.lam b .type (.const "Nat")))

/-! ## Bet (b) check 2 — the three α-comparison sites on canonical `Term`s

    `piAgree`, `checkArm` and `sealRec` compare `Term`s with `Term.alphaEq`, and
    R1 changes what those `Term`s ARE: today a hand-written or macro-elaborated
    type, under R1 also a readback product with `§`-level binders and `§σ` free
    names. The question is whether `alphaEq` still says what it means to say on
    that vocabulary. Three properties, each a way it could fail. -/

def alphaEqOnCanonical : Bool :=
  -- (1) α: two readback-shaped spellings of one function are equal.
  Term.alphaEq (.lam "§0" (.const "Nat") (.pvar "§0")) (.lam "§1" (.const "Nat") (.pvar "§1"))
  -- (2) σ-names are FREE names and compare by spelling, which is what makes two
  --     different σ's two different types rather than α-variants.
  && !Term.alphaEq (.pvar (symName 3)) (.pvar (symName 4))
  && Term.alphaEq (.pvar (symName 3)) (.pvar (symName 3))
  -- (3) a σ-name free in a body is NOT captured by a binder of any minted shape.
  && mintedBinders.all (fun b =>
       !Term.alphaEq (.lam b .type (.pvar (symName 0))) (.lam b .type (.pvar b)))
  -- (4) the mixed case the sites actually meet: a written type against the
  --     readback of the same type.
  && Term.alphaEq (.pi "x" (.const "Nat") (.app (.const "P") (.pvar "x")))
       (.pi "§0" (.const "Nat") (.app (.const "P") (.pvar "§0")))

/-! ## Bet (b) check 3 — round-trip on the shapes that actually rest in Ω -/

def sampleAtRest : List Val :=
  [ .sym 3, .bot, .loanM 2, .borrowM 1 (Val.cons (Val.nat 3) Val.nil)
  , Val.cons (.sym 0) Val.nil
  , .app (.app (.const "Leb") (.sym 0)) (Val.nat 2)
  , .lam "x" (.const "Nat") (.pvar "x")
  , .pi "§0" (.const "Nat") (.app (.const "P") (.pvar "§0"))
  , .idT (.const "Nat") (.sym 1) (Val.nat 2)
  , .cmpT (.const "Nat")
  , .ctor "§segs" [Val.segNode (Val.nat 1) (.ctor "Arr" [.sym 4])
                  , Val.segNode (Val.nat 1) (.loanM 0)]
  , .rfn [⟨0, "v"⟩] (.var ⟨0, "v"⟩)
  , .closure [("L", .app (.const "Len") (.sym 5))] (.app (.const "Add") (.pvar "L")) ]

def roundTripAll : Bool := sampleAtRest.all roundTrips

/-! ## Bet (c) — raw closures at rest, conversion on demand

    Today a pure λ value at rest is closure-free readback syntax: `Pure.lean`'s
    exported entry points (`nfN`, `whnfOut`, `instBodyOut`) read back, so no
    closure crosses out of the normalizer. §2.3 wants the closure to REST and
    conversion to cook transiently.

    The two forms of one builder-style λ. `rawClo` is what M32 wants stored;
    `cooked` is what today's kernel stores for the same source. The λ node is
    kept around the closure (rather than the closure BEING the λ) purely so the
    probe can drive today's `eval`/`readback` unmodified — the representation
    question §2.2 settles is orthogonal to every question below. -/

def listNat : Val := .app (.const "List") (.const "Nat")

/-- ρ holds the SPINE: `L ↦ Len σ5`. The spine is materialized in the value. -/
def rhoSpine : Val.PEnv := [("L", .app (.const "Len") (.sym 5))]

/-- ρ holds the INGREDIENT: `S ↦ σ5`, and the body mints `Len S` on demand.
    This is §3's non-commuting case — "a raw body + ρ holds the spine's
    INGREDIENTS and can re-mint the spine after the sweep has passed". -/
def rhoIngredient : Val.PEnv := [("S", .sym 5)]

def bodySpine : Val := .app (.app (.const "Add") (.pvar "L")) (.pvar "a")
def bodyIngredient : Val :=
  .app (.app (.const "Add") (.app (.const "Len") (.pvar "S"))) (.pvar "a")

def rawSpine : Val := .lam "a" listNat (.closure rhoSpine bodySpine)
def rawIngredient : Val := .lam "a" listNat (.closure rhoIngredient bodyIngredient)

/-- The eager (today's) form of the same λ: closure discharged by readback. -/
def cook (v : Val) : Val := Val.nfV 1000 v

def cookedSpine : Val := cook rawSpine
def cookedIngredient : Val := cook rawIngredient

/-- Apply a λ value to an argument, cooking whatever it takes. -/
def applyTo (f arg : Val) : Val :=
  match f with
  | .lam x _ b => Val.instBodyOut 1000 x b arg
  | _ => .bot

/-! ### (c.i) Do the comparison sites still answer correctly?

    `convert` is `nfV a == nfV b`, and `nfV` is `readback ∘ eval`: `eval` leaves
    a closure in body position alone (`mkClosure` is idempotent on one) and
    `readback` opens the binder through `instBody`, which evaluates the raw body
    under ρ. **So today's `convert` ALREADY cooks transiently** — the raw form
    and the cooked form of one λ convert, and two different λs do not. -/
def cRawConvertsCooked : Bool :=
  Val.convert 1000 rawSpine cookedSpine
    && Val.convert 1000 rawIngredient cookedIngredient
    && !Val.convert 1000 rawSpine (.lam "a" listNat (.pvar "a"))
    -- and it is not vacuous: the two builders differ from each other only in
    -- where the spine lives, and they mean the same function, so they convert.
    && Val.convert 1000 rawSpine rawIngredient

/-! ### (c.ii) Does a refinement sweep through ρ propagate?

    §3: substitution is atom-keyed, every representation preserves atoms, so it
    commutes with evaluation. Measured both ways round: refine-then-apply on the
    RAW form against cook-then-refine-then-apply on the EAGER form. -/
def refineThenApply (v : Val) (arg : Val) : Val :=
  cook (applyTo (substSym 5 (Val.nat 3) v) arg)

def cRefinementCommutes : Bool :=
  refineThenApply rawSpine (Val.nat 7) == refineThenApply cookedSpine (Val.nat 7)
    && refineThenApply rawIngredient (Val.nat 7) == refineThenApply cookedIngredient (Val.nat 7)
    -- the refinement really reached the captured ρ (σ5 is gone from the answer)
    && (refineThenApply rawIngredient (Val.nat 7)).symIds == []

/-! ### (c.iii) The non-commuting hazard, reproduced deliberately

    Generalize the spine `Len σ5 ↦ σ99` across the state, then apply. The eager
    form speaks σ99; the raw form re-mints `Len σ5` from ρ's ingredients and
    speaks the pre-generalization vocabulary. `abstractInto` descends captured
    environments (Machine.lean's closure arm), which is why the MATERIALIZED
    case survives and only the LATENT one diverges — the sharpest available
    statement of what cooking-at-generalization has to buy. -/
def genTarget : Val := .app (.const "Len") (.sym 5)

def genThenApply (v : Val) (arg : Val) : Val :=
  cook (applyTo (abstractInto genTarget 99 v) arg)

/-- The spine materialized in ρ: the sweep reaches it, raw and cooked agree. -/
def cGenMaterializedAgrees : Bool :=
  genThenApply rawSpine (Val.nat 7) == genThenApply cookedSpine (Val.nat 7)

/-- The spine latent in the body: the sweep misses it and the two disagree —
    §3's claim, and the reason cooking must be persistent at generalization. -/
def cGenLatentDiverges : Bool :=
  genThenApply rawIngredient (Val.nat 7) != genThenApply cookedIngredient (Val.nat 7)

/-- And the divergence is exactly the one predicted: the cooked side names σ99,
    the raw side has re-minted a term still mentioning σ5. -/
def cGenLatentShape : Bool :=
  (genThenApply cookedIngredient (Val.nat 7)).symIds == [99]
    && (genThenApply rawIngredient (Val.nat 7)).symIds == [5]

/-- Cooking the closure BEFORE the sweep repairs it — the write-back schedule of
    §3, stated as the property it has to have. -/
def cCookAtGenRepairs : Bool :=
  genThenApply (cook rawIngredient) (Val.nat 7)
    == genThenApply cookedIngredient (Val.nat 7)

/-! ## Bet (a) — the four soundness holes, as programs

    The whole corpus is the net; these are the shapes it might not contain, and
    each is one of the hazards §5 names. They are printed rather than asserted,
    so the id-keyed answer is recorded on this branch and the name-keyed answer
    is compared against it. -/

/-- (a.1) **A match-arm binder shadowing an outer binding of the same name** —
    Stage 0's addendum item 4, the case the arm SEAM buys. `y` must be the outer
    `h`, not the arm's. Under name-keying without the seam it would be the
    arm's. -/
def aShadowArm : Term := prog{
  let h = 5;
  let x = Cons(1, Nil);
  match x { Nil => (), Cons(h, t) => () };
  let y = h;
  () }

/-- (a.2) **Two `let`s of one name in one scope** — both live, and newest-wins
    is simply correct (Stage 0 addendum item 4's non-hazard). -/
def aShadowLet : Term := prog{ let a = 1; let a = 2; let b = a; () }

/-- (a.3) **Recursion — two live frames of one function.** The executing side of
    `Traces`/`Diff` covers this at scale; this is the smallest witness, and the
    one whose Ω a reader can check by eye. -/
def aRecursion : Term := prog{
  fn CountDown [fuel] (fuel : Nat) -> Nat {
    match fuel { Z => Z, S(f2) => { let r = CountDown(f2); S(r) } } };
  let n = CountDown(3);
  () }

/-- (a.4) **A caller local whose NAME is a callee parameter's.** This is the
    `readCWith` site: it PREPENDS the instantiation so that it shadows caller
    slots by ID. Under rightmost-wins name-keying prepending shadows the wrong
    way round, so the instantiation has to be APPENDED — and if it is not, this
    program is where it shows.

    A proof of `Le 2 3` is `unit`: `Le` COMPUTES (`Z ≤ _ ↦ Unit`), so the
    parameter type `Le n 3` is exactly the thing that has to be read at the
    ACTUAL — read it at the caller's `n = 9` instead and it computes to `Bot`,
    which `unit` does not inhabit. The program is therefore a live discriminator
    between the two shadowing directions rather than a shape that merely looks
    like one. -/
def aCallerNameClash : Term := prog{
  fn Ident (n : Nat, h : Le n 3) -> Nat { n };
  fn Caller () -> Nat { let n = 9; let q = Ident(2, unit); q };
  () }

def showPaths (t : Term) : String := toString (tailEnvs t)

#eval s!"(a.1) shadow-arm   : {showPaths aShadowArm}"
#eval s!"(a.2) shadow-let   : {showPaths aShadowLet}"
#eval s!"(a.3) recursion    : {showPaths aRecursion}"
#eval s!"(a.4) name-clash ok: {progOk aCallerNameClash}"

/-! ## The probe's report card -/

#eval s!"(b) sigmaNamesDisjoint            = {sigmaNamesDisjoint}"
#eval s!"(b) substPReachesUnderMinted      = {substPReachesUnderMintedBinders}"
#eval s!"(b) alphaEqOnCanonical            = {alphaEqOnCanonical}"
#eval s!"(b) roundTripAll                  = {roundTripAll}"
#eval s!"(b) roundTrip per sample          = {sampleAtRest.map roundTrips}"
#eval s!"(c.i)   rawConvertsCooked         = {cRawConvertsCooked}"
#eval s!"(c.ii)  refinementCommutes        = {cRefinementCommutes}"
#eval s!"(c.iii) genMaterializedAgrees     = {cGenMaterializedAgrees}"
#eval s!"(c.iii) genLatentDiverges         = {cGenLatentDiverges}"
#eval s!"(c.iii) genLatentShape            = {cGenLatentShape}"
#eval s!"(c.iii) cookAtGenRepairs          = {cCookAtGenRepairs}"
#eval s!"(c.iii) latent raw  = {(genThenApply rawIngredient (Val.nat 7)).pretty}"
#eval s!"(c.iii) latent cook = {(genThenApply cookedIngredient (Val.nat 7)).pretty}"

end Dllbc.StageV
