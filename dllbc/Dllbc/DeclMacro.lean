import Lean
import Dllbc.Machine
import Dllbc.Macro

/-!
# `decl{ … }` — a surface macro for whole `Decl`s (§5 boundaries)

Where `dllbc{ }` (Macro.lean) gives runtime-body surface and `pure{ }`
(PureMacro.lean) gives pure-term surface, `decl{ }` assembles a whole function
**declaration**: the header `fn NAME (x : τ, …) -> τret`, an optional `back = …`
backward spec, and the body — producing the same `Decl` value the corpus builds
by hand. Its reason to exist is removing the ugliness of hand-writing
telescopes like `("hbnd", LeT (addTmH (V 2 "lo") (V 3 "cnt")) (lenT dv))`.

## Type positions (`dty`)

Telescope entry types, the return type, the `↝` right-hand side, and `back`
terms all elaborate through one grammar, `dty` — a pterm-like grammar (Σ/Π/λ/→/
Id/application/`Type`) extended with two things the boundary needs:

  * a **runtime-var context**: the names of EARLIER telescope parameters resolve
    to `.var ⟨i, name⟩` with positional 0-based ids — the exact convention
    `seedTelescope` seeds (argument `i` ↦ var id `i`) and the corpus's `V i "…"`
    references use. Runtime vars are absolute ids, so crossing a Σ/Π/λ binder
    does NOT shift them (matching §5.2: a runtime var in a type is resolved by ⇝
    to its snapshot, never de Bruijn).
  * `*x` in type position → `.deref (.var ⟨i, name⟩)` — the comptime deref the
    corpus writes as `dv`/`lenT (.deref (.var vv))`.

`&mut τ` is `borrowT τ (weaken τ)` (the corpus's plain-borrow encoding; for the
closed telescope types in the corpus `weaken τ` computes to `τ`, so the produced
value is identical). `&mut (τ ~> S)` gives an S that ignores the snapshot;
`&mut (s : τ ~> S)` binds `s` as pure var 0 in `S` — the `borrowT`/`seedTelescope`
convention in Syntax.lean.

## Resolution discipline (och's law)

Every identifier resolves or errors: pure binder → `pvar`; earlier telescope
param → `var`; known constructor → `ctorApp`; kernel const → `const`; a friendly
reified-function alias (`Le`, `len`, `add`, …) → its `…FnT` Term constant; else
the **Lean identifier** of that name, which must denote a `Dllbc.Term` in scope
(a library lemma like `swapL`, `set`, `sortRangeL`) — the documented fallback.

## Body

Reuses the existing `dllbc` block category with the telescope names pre-bound in
order — literally `Dllbc.Macro.expandB` seeded like `dllbcWith`. Bodies laden
with pure proof terms (a `botElim` ex-falso branch, a `le_rw_r` bound derivation)
are outside the runtime `dllb` grammar; for those the escape hatch `= %term`
splices a raw `Term`. See SDeclMacro.lean's header for the coverage map.
-/

open Lean

namespace Dllbc

/-! ## The `dty` grammar (type / back positions) -/

declare_syntax_cat dty

syntax:max ident : dty
syntax:max "(" dty ")" : dty
syntax:max "Type" : dty
syntax:max "%" term:max : dty                                 -- splice a Lean `Term`
syntax:max "*" ident : dty                                    -- comptime deref of a runtime var
syntax:max "Id" dty:max dty:max dty:max : dty                 -- Id A a b
syntax:65 dty:65 dty:66 : dty                                 -- application (left-assoc)
syntax:70 "&mut" dty:65 : dty                                 -- plain borrow  &mut τ
syntax:70 "&mut" "(" dty "~>" dty ")" : dty                   -- &mut (τ ↝ S)      (S ignores s)
syntax:70 "&mut" "(" ident ":" dty "~>" dty ")" : dty         -- &mut (s : τ ↝ S)  (s = pvar 0 in S)
syntax:10 "λ" "(" ident ":" dty ")" "." dty:10 : dty          -- lambda
syntax:10 "Π" "(" ident ":" dty ")" "→" dty:10 : dty          -- Pi
syntax:10 "Σ" "(" ident ":" dty ")" "→" dty:10 : dty          -- Sigma (arrow form)
syntax:10 "Σ" "(" ident ":" dty ")" "." dty:10 : dty          -- Sigma (dot form, as the doc writes it)
syntax:10 dty:11 "→" dty:10 : dty                             -- non-dependent arrow (right-assoc)

namespace DeclMacro
open Lean

/-- Innermost-first de Bruijn index of `s` in `l`. -/
def idxOf? (l : List String) (s : String) : Option Nat :=
  let rec go : List String → Nat → Option Nat
    | [], _ => none
    | x :: xs, i => if x == s then some i else go xs (i + 1)
  go l 0

/-- Kernel constructors → `ctorApp`. -/
def ctorSet : List String := ["Z", "S", "Nil", "Cons", "Pair", "Refl", "True", "False", "unit"]
/-- Kernel constants (type formers / recursors / eliminators) → `const`. -/
def constSet : List String := ["Nat", "Bool", "List", "Bot", "Unit", "natRec", "boolRec", "listRec", "botElim", "j", "k"]
/-- Friendly aliases for the reified library functions whose surface name differs
    from their `…FnT` Term-constant (`Le` ↦ `LeFnT`, etc.). Everything else falls
    through to the raw-Lean-identifier resolution, so lemma Terms (`swapL`, `set`,
    `sortRangeL`, …) are referenced by their own names via the use-site `open`s. -/
def aliasMap : List (String × Name) :=
  [("Le", `Dllbc.Std.LeFnT), ("len", `Dllbc.Std.lenFnT), ("add", `Dllbc.Std.addFnT),
   ("leb", `Dllbc.Std.lebFnT), ("count", `Dllbc.Std.countFnT), ("eqb", `Dllbc.Std.eqbFnT),
   ("take", `Dllbc.Std.takeFnT), ("drop", `Dllbc.Std.dropFnT),
   ("Sorted", `Dllbc.Std.SortedFnT), ("Bound", `Dllbc.Std.BoundFnT)]

/-- Resolve a bare identifier in a type/back position. Pure binder (innermost) →
    `pvar`; earlier telescope param → `var`; constructor → nullary `ctorApp`;
    kernel const → `const`; reified-function alias → its `…FnT` Term; else the
    Lean identifier of that name (a `Term` in scope). -/
def resolveName (rctx : List (String × Nat)) (pctx : List String) (x : Ident) : MacroM (TSyntax `term) := do
  let s := x.getId.toString
  match idxOf? pctx s with
  | some i => `(Dllbc.Term.pvar $(quote i))
  | none =>
    match rctx.lookup s with
    | some id => `(Dllbc.Term.var ⟨$(quote id), $(quote s)⟩)
    | none =>
      if ctorSet.contains s then `(Dllbc.Term.ctorApp $(quote s) [])
      else if constSet.contains s then `(Dllbc.Term.const $(quote s))
      else match aliasMap.lookup s with
        | some n => pure ⟨(mkIdent n).raw⟩
        | none => pure ⟨x.raw⟩

/-- Resolve `*x`: `x` must be a runtime (borrow) parameter in scope. -/
def resolveDeref (rctx : List (String × Nat)) (x : Ident) : MacroM (TSyntax `term) := do
  let s := x.getId.toString
  match rctx.lookup s with
  | some id => `(Dllbc.Term.deref (Dllbc.Term.var ⟨$(quote id), $(quote s)⟩))
  | none => Macro.throwErrorAt x s!"decl: *{s} — '{s}' is not a borrow parameter in scope"

/-- Unfold a left-nested `dty` application into (head, args-in-order). -/
partial def collectApp : TSyntax `dty → TSyntax `dty × Array (TSyntax `dty)
  | `(dty| $f:dty $a:dty) => let (h, as) := collectApp f; (h, as.push a)
  | t => (t, #[])

/-- Elaborate a `dty` under a runtime-var context (`rctx`, name → positional id)
    and a pure-binder context (`pctx`, innermost name first). -/
partial def elabDty (rctx : List (String × Nat)) (pctx : List String) (stx : TSyntax `dty) : MacroM (TSyntax `term) := do
  match stx with
  | `(dty| ($e:dty)) => elabDty rctx pctx e
  | `(dty| Type) => `(Dllbc.Term.type)
  | `(dty| % $e:term) => `(($e : Dllbc.Term))
  | `(dty| * $x:ident) => resolveDeref rctx x
  | `(dty| Id $a:dty $b:dty $c:dty) => do
    `(Dllbc.Term.idT $(← elabDty rctx pctx a) $(← elabDty rctx pctx b) $(← elabDty rctx pctx c))
  | `(dty| &mut ( $x:ident : $τ:dty ~> $s:dty )) => do
    let τT ← elabDty rctx pctx τ
    let sT ← elabDty rctx (x.getId.toString :: pctx) s
    `(Dllbc.Term.borrowT $τT $sT)
  | `(dty| &mut ( $τ:dty ~> $s:dty )) => do
    let τT ← elabDty rctx pctx τ
    let sT ← elabDty rctx pctx s
    `(Dllbc.Term.borrowT $τT (Dllbc.Term.shiftPure 1 0 $sT))
  | `(dty| &mut $τ:dty) => do
    let τT ← elabDty rctx pctx τ
    `(Dllbc.Term.borrowT $τT (Dllbc.Term.shiftPure 1 0 $τT))
  | `(dty| λ ($x:ident : $τ:dty). $b:dty) => do
    `(Dllbc.Term.lam $(← elabDty rctx pctx τ) $(← elabDty rctx (x.getId.toString :: pctx) b))
  | `(dty| Π ($x:ident : $τ:dty) → $b:dty) => do
    `(Dllbc.Term.pi $(← elabDty rctx pctx τ) $(← elabDty rctx (x.getId.toString :: pctx) b))
  | `(dty| Σ ($x:ident : $τ:dty) → $b:dty) => do
    `(Dllbc.Term.sigmaT $(← elabDty rctx pctx τ) $(← elabDty rctx (x.getId.toString :: pctx) b))
  | `(dty| Σ ($x:ident : $τ:dty). $b:dty) => do
    `(Dllbc.Term.sigmaT $(← elabDty rctx pctx τ) $(← elabDty rctx (x.getId.toString :: pctx) b))
  | `(dty| $a:dty → $b:dty) => do
    `(Dllbc.Term.pi $(← elabDty rctx pctx a) $(← elabDty rctx ("_" :: pctx) b))
  | `(dty| $_:dty $_:dty) => do                     -- application spine
    let (head, args) := collectApp stx
    let argTerms ← args.toList.mapM (elabDty rctx pctx)
    match head with
    | `(dty| $h:ident) =>
      let hs := h.getId.toString
      if ctorSet.contains hs && (idxOf? pctx hs).isNone && (rctx.lookup hs).isNone then
        let argArr := argTerms.toArray
        `(Dllbc.Term.ctorApp $(quote hs) [$argArr,*])
      else
        let hterm ← resolveName rctx pctx h
        argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
    | _ =>
      let hterm ← elabDty rctx pctx head
      argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
  | `(dty| $x:ident) => resolveName rctx pctx x
  | _ => Macro.throwErrorAt stx "decl: unexpected type/term syntax"

/-- Build the telescope entry syntaxes, threading the runtime-var context so that
    parameter `i`'s type sees exactly params `0 .. i-1` (each at its positional
    id) — the `seedTelescope` convention. -/
partial def buildTele (rctx : List (String × Nat)) (i : Nat) :
    List (String × TSyntax `dty) → MacroM (Array (TSyntax `term))
  | [] => pure #[]
  | (nm, τ) :: rest => do
    let τT ← elabDty rctx [] τ
    let entry ← `((($(quote nm), $τT) : String × Dllbc.Term))
    let rest' ← buildTele (rctx ++ [(nm, i)]) (i + 1) rest
    pure (#[entry] ++ rest')

end DeclMacro

/-! ## The `decl{ … }` declaration surface -/

declare_syntax_cat declParam
declare_syntax_cat declBody

syntax ident ":" dty : declParam
syntax "{" dllb "}" : declBody              -- runtime body (reuses the `dllbc` block)
syntax "=" "%" term : declBody              -- escape hatch: splice a raw `Term` body

syntax "decl{" "fn" ident "(" declParam,* ")" "->" dty declBody "}" : term
syntax "decl{" "fn" ident "(" declParam,* ")" "->" dty "back" "=" dty declBody "}" : term

namespace DeclMacro
open Lean

/-- Shared assembly: build the `Decl` term from its parsed pieces. -/
def assemble (name : Ident) (params : Array (TSyntax `declParam)) (ret : TSyntax `dty)
    (bk : Option (TSyntax `dty)) (body : TSyntax `declBody) : MacroM (TSyntax `term) := do
  let parsed ← params.toList.mapM fun (p : TSyntax `declParam) => match p with
    | `(declParam| $x:ident : $τ:dty) => pure (x.getId.toString, τ)
    | _ => Macro.throwErrorAt p "decl: malformed parameter (expected `x : τ`)"
  let names := parsed.map (·.1)
  let n := names.length
  let fullRctx : List (String × Nat) := names.zip (List.range n)
  let teleSyns ← buildTele [] 0 parsed                      -- each entry sees only earlier params
  let retT ← elabDty fullRctx [] ret                        -- retType sees the whole telescope
  let backT ← match bk with
    | some b => do let bt ← elabDty fullRctx [] b; `(some $bt)
    | none   => `((none : Option Dllbc.Term))
  let bodyT ← match body with                               -- `dllb` block (like dllbcWith) or `%` splice
    | `(declBody| { $b:dllb }) => do let (t, _) ← Dllbc.Macro.expandB fullRctx n b; pure t
    | `(declBody| = % $t:term) => pure ⟨t.raw⟩
    | _ => Macro.throwErrorAt body "decl: malformed body"
  -- `Decl.mk` positionally (name, telescope, retType, body, back): a structure
  -- literal `{ … back := … }` cannot be written here, since declaring the surface
  -- keyword `back` reserves the token, colliding with the field name.
  `(Dllbc.Decl.mk $(quote name.getId.toString) [$teleSyns,*] $retT $bodyT $backT)

end DeclMacro

open DeclMacro in
macro_rules
  | `(decl{ fn $name:ident ( $params,* ) -> $ret:dty $body:declBody }) =>
    assemble name params.getElems ret none body
  | `(decl{ fn $name:ident ( $params,* ) -> $ret:dty back = $bk:dty $body:declBody }) =>
    assemble name params.getElems ret (some bk) body

end Dllbc
