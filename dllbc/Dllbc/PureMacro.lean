import Lean
import Dllbc.Syntax

/-!
# `pure{ … }` — named-binder surface syntax for the pure fragment (§15)

The M11 wall was mis-indexed de Bruijn failing silently across ~15 binder
contexts. The fix is not a unifier or case trees — it is *names and explicit
structure*, elaborated to the existing de Bruijn kernel `Term` by the macro
layer, in exactly the resolve-or-error discipline `dllbc{ }` already uses for
runtime code. This is authoring sugar, nothing more: every binder is named,
every motive is written once and explicitly, and a wrong motive fails at the use
site with the existing conversion diagnostics.

Name resolution for a bare identifier `x`:
  * a **bound** name → its de Bruijn `pvar` (index = binders since it was bound);
  * a known **constructor** (`Z`, `S`, `Cons`, `Refl`, `unit`, …) → `ctorApp`;
  * a kernel **constant** (`Nat`, `List`, `natRec`, `j`, …) → `const`;
  * anything else → the **Lean identifier** of that name, which must denote a
    `Dllbc.Term` in scope (a library definition like `Le`); an unbound name is a
    Lean elaboration error, never a silent fallback.

`%e` splices a Lean-level `Term` expression `e` directly (an escape hatch).

The recursor sugar `elim` lives in this file too (§15b).
-/

open Lean

namespace Dllbc

/-! ## The `pterm` grammar -/

declare_syntax_cat pterm
declare_syntax_cat pelimArm

syntax:max ident : pterm
syntax:max "(" pterm ")" : pterm
syntax:max "Type" : pterm
syntax:max "%" term:max : pterm                                  -- splice a Lean `Term`
syntax:max "Id" pterm:max pterm:max pterm:max : pterm            -- Id A a b
syntax:65 pterm:65 pterm:66 : pterm                              -- application (left-assoc)
syntax:10 "λ" "(" ident ":" pterm ")" "." pterm:10 : pterm       -- lambda
syntax:10 "Π" "(" ident ":" pterm ")" "→" pterm:10 : pterm       -- Pi
syntax:10 "Σ" "(" ident ":" pterm ")" "→" pterm:10 : pterm       -- Sigma
syntax:10 pterm:11 "→" pterm:10 : pterm                          -- non-dependent arrow (right-assoc)
syntax:10 "let" ident "=" pterm ";" pterm:10 : pterm             -- pure let (β-redex)

-- arms: `Ctor (b) (b) … ih => body` ; binders and the recursive `ih` are named.
syntax ident ("(" ident ")")* (ident)? "=>" pterm : pelimArm
-- `elim SCRUT return MOTIVE { arms }` — recursor sugar (§15b).
syntax:max "elim" pterm:max "return" pterm:max "{" pelimArm,* "}" : pterm
-- `elim SCRUT generalizing GOAL { arms }` (§18) — the motive is formed by
-- abstracting SCRUT out of the (un-abstracted, natural) GOAL, at all occurrences.
syntax:max "elim" pterm:max "generalizing" pterm:max "{" pelimArm,* "}" : pterm

syntax "pure{" pterm "}" : term

namespace PureMacro
open Lean

/-- Index of `s` in `l` (innermost-first de Bruijn), if present. -/
def idxOf? (l : List String) (s : String) : Option Nat :=
  let rec go : List String → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x == s then some i else go xs (i + 1)
  go l 0

/-- Kernel constructors → `ctorApp`. -/
def ctorSet : List String := ["Z", "S", "Nil", "Cons", "Pair", "Refl", "True", "False", "unit"]
/-- Kernel constants (type formers and recursors) → `const`. -/
def constSet : List String := ["Nat", "Bool", "List", "Bot", "Unit", "natRec", "boolRec", "listRec", "botElim", "j", "k"]

/-- Resolve a bare identifier: bound → `pvar`, constructor → nullary `ctorApp`,
    kernel constant → `const`, else the Lean identifier (a `Term` in scope). -/
def resolveIdent (ctx : List String) (x : Ident) : MacroM (TSyntax `term) := do
  let s := x.getId.toString
  match idxOf? ctx s with
  | some i => `(Dllbc.Term.pvar $(quote i))
  | none =>
    if ctorSet.contains s then `(Dllbc.Term.ctorApp $(quote s) [])
    else if constSet.contains s then `(Dllbc.Term.const $(quote s))
    else pure ⟨x.raw⟩                                     -- a Lean `Term` def, resolved at use site

/-- Unfold a left-nested application into (head, args-in-order). -/
partial def collectApp : TSyntax `pterm → TSyntax `pterm × Array (TSyntax `pterm)
  | `(pterm| $f:pterm $a:pterm) => let (h, as) := collectApp f; (h, as.push a)
  | t => (t, #[])

mutual

/-- Elaborate a `pterm` under a binder context (innermost name first). -/
partial def elabP (ctx : List String) (stx : TSyntax `pterm) : MacroM (TSyntax `term) := do
  match stx with
  | `(pterm| ($e:pterm)) => elabP ctx e
  | `(pterm| Type) => `(Dllbc.Term.type)
  | `(pterm| % $e:term) => `(($e : Dllbc.Term))
  | `(pterm| Id $a:pterm $b:pterm $c:pterm) => do
    `(Dllbc.Term.idT $(← elabP ctx a) $(← elabP ctx b) $(← elabP ctx c))
  | `(pterm| λ ($x:ident : $τ:pterm). $b:pterm) => do
    `(Dllbc.Term.lam $(← elabP ctx τ) $(← elabP (x.getId.toString :: ctx) b))
  | `(pterm| Π ($x:ident : $τ:pterm) → $b:pterm) => do
    `(Dllbc.Term.pi $(← elabP ctx τ) $(← elabP (x.getId.toString :: ctx) b))
  | `(pterm| Σ ($x:ident : $τ:pterm) → $b:pterm) => do
    `(Dllbc.Term.sigmaT $(← elabP ctx τ) $(← elabP (x.getId.toString :: ctx) b))
  | `(pterm| $a:pterm → $b:pterm) => do
    -- Non-dependent arrow = Π over an unused binder; the fresh "_" slot shifts
    -- `b`'s de Bruijn indices up by one for free.
    `(Dllbc.Term.pi $(← elabP ctx a) $(← elabP ("_" :: ctx) b))
  | `(pterm| let $x:ident = $e:pterm ; $b:pterm) => do
    -- β-redex `(λ (_ : Type). b) e`; the dummy domain is erased under reduction.
    `(Dllbc.Term.app (Dllbc.Term.lam Dllbc.Term.type $(← elabP (x.getId.toString :: ctx) b)) $(← elabP ctx e))
  | `(pterm| elim $scrut:pterm return $motive:pterm { $arms,* }) =>
    elabElim ctx scrut motive arms.getElems
  | `(pterm| elim $scrut:pterm generalizing $goal:pterm { $arms,* }) =>
    elabGenElim ctx scrut goal arms.getElems
  | `(pterm| $_:pterm $_:pterm) => do              -- application spine
    let (head, args) := collectApp stx
    let argTerms ← args.toList.mapM (elabP ctx)
    match head with
    | `(pterm| $h:ident) =>
      let hs := h.getId.toString
      if ctorSet.contains hs && !(ctx.contains hs) then
        let argArr := argTerms.toArray
        `(Dllbc.Term.ctorApp $(quote hs) [$argArr,*])
      else
        let hterm ← resolveIdent ctx h
        argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
    | _ => do
      let hterm ← elabP ctx head
      argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
  | `(pterm| $x:ident) => resolveIdent ctx x
  | _ => Macro.throwErrorAt stx "pure: unexpected term syntax"

/-- Elaborate `elim scrut return motive { arms }` to the matching recursor. §15b.
    The arm binder DOMAINS are derived from the recursor scheme and the motive —
    determined, not inferred: a natRec `S` step is `λ (k : Nat). λ (ih : P k). …`,
    a listRec `Cons` step is `λ (h : Nat). λ (t : List Nat). λ (ih : P t). …`.
    `P k`/`P t` are built by re-elaborating the motive BODY in a context whose
    position-0 name is the motive's binder — de Bruijn-correct regardless of the
    arm's chosen binder names. -/
partial def elabElim (ctx : List String) (scrut motive : TSyntax `pterm)
    (arms : Array (TSyntax `pelimArm)) : MacroM (TSyntax `term) := do
  let scrutT ← elabP ctx scrut
  let motiveT ← elabP ctx motive
  -- The motive is `(λ (m : τ). MP)` (parenthesized, since it sits at max prec);
  -- keep the binder name and body for the arm domains.
  let motiveBare := match motive with | `(pterm| ($e:pterm)) => e | _ => motive
  let (mName, mBody) ← match motiveBare with
    | `(pterm| λ ($x:ident : $_τ:pterm). $b:pterm) => pure (x.getId.toString, b)
    | _ => Macro.throwError "elim: motive must be a λ `(x : τ). …`"
  let armFor (c : String) : MacroM (Option (Array Ident × Option Ident × TSyntax `pterm)) := do
    for arm in arms do
      match arm with
      | `(pelimArm| $ctor:ident $[($bs:ident)]* $[$ih:ident]? => $body:pterm) =>
        if ctor.getId.toString == c then return some (bs, ih, body)
      | _ => pure ()
    return none
  let getArm (c : String) : MacroM (Array Ident × Option Ident × TSyntax `pterm) := do
    match ← armFor c with
    | some r => pure r
    | none => Macro.throwError s!"elim: missing arm for constructor '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(pelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:pterm) => some ctor.getId.toString
    | _ => none)
  -- `P applied to the substructure`, as the recursive binder's domain: the motive
  -- body elaborated with `mName` at position 0, under `depth` leading binders.
  let pOf (leading : List String) : MacroM (TSyntax `term) := elabP (mName :: leading ++ ctx) mBody
  if names.contains "Z" || names.contains "S" then
    let (_, _, zb) ← getArm "Z"
    let z ← elabP ctx zb
    let (sb, sih, sbody) ← getArm "S"
    let kName := (sb.get! 0).getId.toString
    let ihName := (sih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf []                                       -- P k  (k at pvar 0)
    let body ← elabP (ihName :: kName :: ctx) sbody
    `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "natRec") $motiveT) $z)
        (Dllbc.Term.lam (Dllbc.Term.const "Nat") (Dllbc.Term.lam $ihDom $body))) $scrutT)
  else if names.contains "True" || names.contains "False" then
    let (_, _, tb) ← getArm "True"; let t ← elabP ctx tb
    let (_, _, fb) ← getArm "False"; let f ← elabP ctx fb
    `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motiveT) $t) $f) $scrutT)
  else if names.contains "Nil" || names.contains "Cons" then
    let (_, _, nb) ← getArm "Nil"; let n ← elabP ctx nb
    let (cb, cih, cbody) ← getArm "Cons"
    let hName := (cb.get! 0).getId.toString
    let tName := (cb.get! 1).getId.toString
    let ihName := (cih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf [hName]                                  -- P t  (t at pvar 0, h at pvar 1)
    let body ← elabP (ihName :: tName :: hName :: ctx) cbody
    `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "listRec") (Dllbc.Term.const "Nat")) $motiveT) $n)
        (Dllbc.Term.lam (Dllbc.Term.const "Nat") (Dllbc.Term.lam (Dllbc.Term.app (Dllbc.Term.const "List") (Dllbc.Term.const "Nat")) (Dllbc.Term.lam $ihDom $body)))) $scrutT)
  else
    Macro.throwError "elim: arms do not match a known recursor (Nat/Bool/List)"

/-- `elim SCRUT generalizing GOAL { arms }` (§18): the motive is
    `λ x. abstractOccurrences SCRUT GOAL` — the natural goal with the computed
    subterm abstracted at all its occurrences, mechanically. Bool motives only
    for now (the count algebra's case-on-`eqb`); Nat/List use the `return` form. -/
partial def elabGenElim (ctx : List String) (scrut goal : TSyntax `pterm)
    (arms : Array (TSyntax `pelimArm)) : MacroM (TSyntax `term) := do
  let scrutT ← elabP ctx scrut
  let goalT ← elabP ctx goal
  let armBody (c : String) : MacroM (TSyntax `term) := do
    for arm in arms do
      match arm with
      | `(pelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $body:pterm) =>
        if ctor.getId.toString == c then return (← elabP ctx body)
      | _ => pure ()
    Macro.throwError s!"elim generalizing: missing arm '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(pelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:pterm) => some ctor.getId.toString
    | _ => none)
  if names.contains "True" || names.contains "False" then
    let t ← armBody "True"
    let f ← armBody "False"
    -- Normalize scrut and goal (`Std.nfTerm`, referenced unhygienically so it
    -- resolves at the use site — the macro layer need not import Std) so a
    -- computed subterm hidden in a definition (`eqb` inside `count`) is exposed
    -- before abstraction. Then abstract at all occurrences.
    let nf := Lean.mkIdent `Dllbc.Std.nfTerm
    let motive ← `(Dllbc.Term.lam (Dllbc.Term.const "Bool")
      (Dllbc.abstractOccurrences ($nf $scrutT) ($nf $goalT)))
    `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motive) $t) $f) $scrutT)
  else
    Macro.throwError "elim generalizing: only Bool motives supported (§18); Nat/List use the `return` form"

end

end PureMacro

macro_rules
  | `(pure{ $e:pterm }) => Dllbc.PureMacro.elabP [] e

end Dllbc
