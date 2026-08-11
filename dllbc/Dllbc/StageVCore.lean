import Dllbc.Pure

/-!
# M32 Stage V — bet (b)'s core: at-rest `Val` ⇄ canonical `Term`

Throwaway probe scaffolding (suspensions.md §5, Stage V bet (b)). It sits below
`Machine` so the canary can route `generalizeStuck`'s sweep through the
`Term`-level twin; everything else about the probe lives in `Dllbc/StageV.lean`.

## The σ namespace

§2.3 wants at-rest knowledge to be a canonical `Term` with σ's as reserved
`§`-names. The namespace must be disjoint from every binder the machine mints,
or `Term.substP`'s "stop at a binder that rebinds the name" guard stops being
vacuous (suspensions.md §6's first sharp edge). The full inventory of reserved
BINDER names in the kernel, grepped rather than remembered:

    `readbackName d` = `§<digits>`    (Syntax.lean)
    `genName`        = `§gen`         (Syntax.lean)
    `letName id`     = `§let<digits>` (Pure.lean)
    `paramName x`    = `§p<digits>`   (FnMacro.lean)
    `unusedSnapName` = `§_`           (Uni.lean)
    `§k §ih §h §t §x §y §n §xs §lo`   (Machine.lean's hand-built recursor
                                       premise types)

`§σ<digits>` misses all of them. `StageV.sigmaNamesDisjoint` asserts it
mechanically. (`§seg`/`§segs` are CONSTRUCTOR names, never binders.)

## Why there are sentinels

The at-rest `Val`s a store-wide sweep meets are NOT all knowledge: Ω holds ⊥,
loan markers, borrows, and (executing) `rfn`s, and `Term` has a form for none of
them. Rather than assume the sweep only meets knowledge, each missing former is
encoded as a reserved-name `ctorApp` sentinel and COUNTED over the corpus. A
sentinel that never fires is a former `Term` does not need; one that fires is a
cost line for R1, named rather than discovered.
-/

namespace Dllbc.StageV

/-- A σ rendered as a reserved pure name. -/
def symName (σ : Nat) : String := "§σ" ++ toString σ

/-- Recognize one. -/
def symOfName? (s : String) : Option Nat :=
  if s.startsWith "§σ" then (s.drop 2).toNat? else none

def sBot : String := "§Vbot"
def sLoan : String := "§VloanM"
def sBorrow : String := "§VborrowM"
def sRfn : String := "§Vrfn"
def sClo : String := "§Vclo"
def sCloEnv : String := "§VcloEnv"

/-- A `Nat` as a term numeral (the sentinels' id payloads). -/
def tNat : Nat → Term
  | 0 => .ctorApp "Z" []
  | k + 1 => .ctorApp "S" [tNat k]

def natOfT? : Term → Option Nat
  | .ctorApp "Z" [] => some 0
  | .ctorApp "S" [t] => (natOfT? t).map (· + 1)
  | _ => none

/-- **At-rest `Val` → canonical `Term`.** Purely structural: at-rest values are
    already closure-free first-order trees (M30's "closures never leave
    `Pure.lean`"), so nothing is evaluated — which is the claim R1 rests on, that
    the at-rest form IS readback output. -/
partial def valToTerm : Val → Term
  | .sym σ => .pvar (symName σ)
  | .pvar x => .pvar x
  | .type => .type
  | .const c => .const c
  | .ctor n args => .ctorApp n (args.map valToTerm)
  | .app f a => .app (valToTerm f) (valToTerm a)
  | .idT a b c => .idT (valToTerm a) (valToTerm b) (valToTerm c)
  | .lam x d b => .lam x (valToTerm d) (valToTerm b)
  | .pi x d c => .pi x (valToTerm d) (valToTerm c)
  | .sigmaT x d c => .sigmaT x (valToTerm d) (valToTerm c)
  | .cmpT τ => .cmpT (valToTerm τ)
  -- `rfn`'s body is already a `Term`, so it rides verbatim; its binders are
  -- untyped (`Val.rfn`'s erasure principle) and get `Type` domains, which is
  -- lossless here because nothing reads a `.lamR` domain out of a value.
  | .bot => .ctorApp sBot []
  | .loanM ℓ => .ctorApp sLoan [tNat ℓ]
  | .borrowM ℓ p => .ctorApp sBorrow [tNat ℓ, valToTerm p]
  | .rfn xs b => .ctorApp sRfn [.lamR (xs.map (fun v => (v, .type))) b]
  | .closure ρ b =>
    .ctorApp sClo [.ctorApp sCloEnv (ρ.map (fun p => .lam p.1 .type (valToTerm p.2))),
                   valToTerm b]

/-- The inverse. Total, and the identity on everything `valToTerm` produces. -/
partial def termToVal : Term → Val
  | .ctorApp n args =>
    if n == sBot then .bot
    else if n == sLoan then
      match args with | [i] => .loanM ((natOfT? i).getD 0) | _ => .bot
    else if n == sBorrow then
      match args with | [i, p] => .borrowM ((natOfT? i).getD 0) (termToVal p) | _ => .bot
    else if n == sRfn then
      match args with | [.lamR xs b] => .rfn (xs.map (·.1)) b | _ => .bot
    else if n == sClo then
      match args with
      | [.ctorApp _ es, b] =>
        .closure (es.filterMap (fun e => match e with
          | .lam x _ v => some (x, termToVal v) | _ => none)) (termToVal b)
      | _ => .bot
    else .ctor n (args.map termToVal)
  | .pvar x => match symOfName? x with | some σ => .sym σ | none => .pvar x
  | .type => .type
  | .const c => .const c
  | .app f a => .app (termToVal f) (termToVal a)
  | .idT a b c => .idT (termToVal a) (termToVal b) (termToVal c)
  | .lam x d b => .lam x (termToVal d) (termToVal b)
  | .pi x d c => .pi x (termToVal d) (termToVal c)
  | .sigmaT x d c => .sigmaT x (termToVal d) (termToVal c)
  | .cmpT τ => .cmpT (termToVal τ)
  | _ => .bot

/-- Round-trip fidelity, the property R1 needs at every boundary. -/
def roundTrips (v : Val) : Bool := termToVal (valToTerm v) == v

/-! ## The `Term`-level `abstractInto` twin

    §19's generalization at the level R1 wants it: abstract every occurrence of
    `target` into the σ-name for `σb`. The `Val` original carries no shadowing
    guard because its targets are pvar-free spines over σ's; at `Term` level the
    same fact reads as "no binder rebinds a `§σ`-name", which is
    `sigmaNamesDisjoint`, so the guard would be vacuous and is left out rather
    than written and never fired.

    **One deliberate asymmetry, and it is the probe's job to report it:**
    `Val.beq` is MODE-BLIND (it unwraps `cmpT` on either side, §6's "case is
    inert under ⇝"), while `Term.beq` is mode-sensitive by design (`absOcc`
    wants to see a marker). So a target `τ` matches an occurrence `⇝τ` under the
    `Val` sweep and not under this one. `genDivergences` measures whether that
    difference is ever reached. -/
/-- POSITIVE CONTROL SWITCH: with this `true`, `abstractIntoT` abstracts
    nothing, so the corpus must go RED and every sweep must report a divergence.
    A green corpus under sabotage would mean the canary proves nothing. -/
def sabotage : Bool := false

partial def abstractIntoT (target : Term) (σb : Nat) (t : Term) : Term :=
  if sabotage then t
  else if Term.beq t target then .pvar (symName σb)
  else match t with
    | .ctorApp n args => .ctorApp n (args.map (abstractIntoT target σb))
    | .app f a => .app (abstractIntoT target σb f) (abstractIntoT target σb a)
    | .idT a b c =>
      .idT (abstractIntoT target σb a) (abstractIntoT target σb b) (abstractIntoT target σb c)
    | .lam x d b => .lam x (abstractIntoT target σb d) (abstractIntoT target σb b)
    | .pi x d c => .pi x (abstractIntoT target σb d) (abstractIntoT target σb c)
    | .sigmaT x d c => .sigmaT x (abstractIntoT target σb d) (abstractIntoT target σb c)
    | .cmpT τ => .cmpT (abstractIntoT target σb τ)
    | s => s

/-- **The canary's routing.** `generalizeStuck`'s per-slot sweep, taken through
    the `Term` level: convert at the boundary, abstract as syntax, convert back.
    If R1's domain split is viable, substituting this for `abstractInto` leaves
    every flagship proof standing. -/
def abstractIntoViaTerm (target : Val) (σb : Nat) (v : Val) : Val :=
  termToVal (abstractIntoT (valToTerm target) σb (valToTerm v))

end Dllbc.StageV
