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

/-! ## The unified `uterm` / `ublk` grammar (§ point 1 — one term/block surface)

One expression grammar whose forms span BOTH the runtime fragment (call/ctorApp/
borrow/deref/match/`()`) and the pure fragment (application spines, λ/Π/Σ/→/Id/
`Type`, lemma & const references). `ublk` is the statement layer (let/assign/seq)
that wraps it. `decl{}`'s body elaborates through this — so `botElim Unit p` and a
`let p2b = le_rw_r … ; …` proof-derivation body are writable DIRECTLY, no splice.

**The one disambiguation rule (§ point 2):** `f(a, b)` — an identifier with a
comma-paren argument list — is a runtime **call** (lowercase head) or **ctorApp**
(uppercase head). Space-separated **juxtaposition** `f a b` is **pure
application** (`ctorApp` when the head is a known constructor). So `nth(&mut *tl,
k, p)` is a call, `botElim Unit p` is an application spine, and `S(*l)` / `S *l`
both mean `ctorApp "S" [*l]`. -/

declare_syntax_cat uterm
declare_syntax_cat ublk
declare_syntax_cat uarm
declare_syntax_cat uarmBody

syntax:max ident : uterm
syntax:max num : uterm
syntax:max "(" ")" : uterm                                    -- unit
syntax:max "(" uterm ")" : uterm                             -- grouping
syntax:max "Type" : uterm
syntax:max "%" term:max : uterm                              -- splice a Lean `Term`
syntax:max "*" uterm:max : uterm                            -- deref / peel
syntax:max "Id" uterm:max uterm:max uterm:max : uterm        -- Id A a b
syntax:max ident "(" uterm,* ")" : uterm                     -- call / ctorApp (comma-paren form)
syntax:70 "&mut" uterm:71 : uterm                            -- runtime borrow  &mut e
syntax:65 uterm:65 uterm:66 : uterm                          -- application (juxtaposition)
syntax:10 "λ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- lambda
syntax:10 "Π" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Pi
syntax:10 "Σ" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Sigma (arrow form)
syntax:10 "Σ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- Sigma (dot form)
syntax:10 uterm:11 "→" uterm:10 : uterm                      -- non-dependent arrow
syntax:max "match" ident "{" uarm,* "}" : uterm              -- runtime match (§3)

syntax "{" ublk "}" : uarmBody                               -- braced block arm body
syntax uterm : uarmBody                                      -- bare expression arm body
syntax ident "=>" uarmBody : uarm                            -- nullary pattern
syntax ident "(" ident,* ")" "=>" uarmBody : uarm            -- applied pattern C(x, y)

syntax "let" ident "=" uterm ";" ublk : ublk                 -- runtime let (→ letIn)
syntax uterm ":=" uterm ";" ublk : ublk                      -- assignment
syntax uterm ";" ublk : ublk                                 -- expression statement (seq)
syntax uterm : ublk                                          -- final expression

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

/-! ## Unified `uterm` / `ublk` elaborators (§ points 1–3)

Runtime binders (let, match patterns) mint fresh absolute ids threaded through
`next` EXACTLY as `Dllbc.Macro.expandB` does — so the runtime subset produces
byte-identical `Term`s to the `dllbc` block, and existing decl bodies keep their
ids. Pure binders (λ/Π/Σ/→) push the de Bruijn `pctx` and never touch `next`; a
runtime var referenced from inside a pure spine stays `.var` (absolute, unshifted). -/

partial def collectAppU : TSyntax `uterm → TSyntax `uterm × Array (TSyntax `uterm)
  | `(uterm| $f:uterm $a:uterm) => let (h, as) := collectAppU f; (h, as.push a)
  | t => (t, #[])

mutual

partial def elabUTerm (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `uterm) : MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(uterm| ()) => return (← `(Dllbc.Term.unit), next)
  | `(uterm| ($e:uterm)) => elabUTerm rctx pctx next e
  | `(uterm| Type) => return (← `(Dllbc.Term.type), next)
  | `(uterm| % $e:term) => return (← `(($e : Dllbc.Term)), next)
  | `(uterm| $n:num) => return (← Dllbc.Macro.buildNat n.getNat, next)
  | `(uterm| * $e:uterm) => do
    let (e', n) ← elabUTerm rctx pctx next e
    return (← `(Dllbc.Term.deref $e'), n)
  | `(uterm| &mut $e:uterm) => do
    let (e', n) ← elabUTerm rctx pctx next e
    return (← `(Dllbc.Term.borrow $e'), n)
  | `(uterm| Id $a:uterm $b:uterm $c:uterm) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (b', n2) ← elabUTerm rctx pctx n1 b
    let (c', n3) ← elabUTerm rctx pctx n2 c
    return (← `(Dllbc.Term.idT $a' $b' $c'), n3)
  | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => do
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.lam $τ' $b'), n2)
  | `(uterm| Π ($x:ident : $τ:uterm) → $b:uterm) => do
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.pi $τ' $b'), n2)
  | `(uterm| Σ ($x:ident : $τ:uterm) → $b:uterm) => do
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $τ' $b'), n2)
  | `(uterm| Σ ($x:ident : $τ:uterm). $b:uterm) => do
    let (τ', n1) ← elabUTerm rctx pctx next τ
    let (b', n2) ← elabUTerm rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $τ' $b'), n2)
  | `(uterm| $a:uterm → $b:uterm) => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (b', n2) ← elabUTerm rctx ("_" :: pctx) n1 b
    return (← `(Dllbc.Term.pi $a' $b'), n2)
  | `(uterm| $c:ident ($args,*)) => do
    let (args', n) ← elabUList rctx pctx next args.getElems.toList
    let name := c.getId.toString
    if Dllbc.Macro.isUpperInit name then
      return (← `(Dllbc.Term.ctorApp $(quote name) [$args',*]), n)
    else
      return (← `(Dllbc.Term.call $(quote name) [$args',*]), n)
  | `(uterm| match $x:ident { $arms,* }) => do
    let s := x.getId.toString
    match rctx.lookup s with
    | none => Macro.throwErrorAt x s!"decl: match scrutinee '{s}' is not a bound runtime variable"
    | some id =>
      let (arms', n) ← elabUArms rctx pctx next arms.getElems.toList
      return (← `(Dllbc.Term.matchE ⟨$(quote id), $(quote s)⟩ [$arms',*]), n)
  | `(uterm| $_:uterm $_:uterm) => do                 -- application spine (juxtaposition)
    let (head, args) := collectAppU stx
    match head with
    | `(uterm| $h:ident) =>
      let hs := h.getId.toString
      let (argTerms, n) ← elabUList rctx pctx next args.toList
      if ctorSet.contains hs && (idxOf? pctx hs).isNone && (rctx.lookup hs).isNone then
        return (← `(Dllbc.Term.ctorApp $(quote hs) [$argTerms,*]), n)
      else
        let hterm ← resolveName rctx pctx h
        let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
        return (out, n)
    | _ => do
      let (hterm, n0) ← elabUTerm rctx pctx next head
      let (argTerms, n) ← elabUList rctx pctx n0 args.toList
      let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
      return (out, n)
  | `(uterm| $x:ident) => return (← resolveName rctx pctx x, next)
  | _ => Macro.throwErrorAt stx "decl: unexpected term syntax"

partial def elabUList (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uterm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUTerm rctx pctx next a
    let (rest, n2) ← elabUList rctx pctx n1 as
    pure (#[a'] ++ rest, n2)

partial def elabUArms (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uarm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUArm rctx pctx next a
    let (rest, n2) ← elabUArms rctx pctx n1 as
    pure (#[a'] ++ rest, n2)

partial def elabUArm (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (arm : TSyntax `uarm) : MacroM (TSyntax `term × Nat) := do
  match arm with
  | `(uarm| $c:ident => $body:uarmBody) => do
    let (body', n) ← elabUArmBody rctx pctx next body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [] $body'), n)
  | `(uarm| $c:ident ($binders,*) => $body:uarmBody) => do
    let (rctx', next', binderVars) ← Dllbc.Macro.mintBinders rctx next binders.getElems.toList
    let (body', n) ← elabUArmBody rctx' pctx next' body
    return (← `(Dllbc.Branch.mk $(quote c.getId.toString) [$binderVars,*] $body'), n)
  | _ => Macro.throwErrorAt arm "decl: unexpected match arm"

partial def elabUArmBody (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (body : TSyntax `uarmBody) : MacroM (TSyntax `term × Nat) := do
  match body with
  | `(uarmBody| { $b:ublk }) => elabUBlk rctx pctx next b
  | `(uarmBody| $e:uterm) => elabUTerm rctx pctx next e
  | _ => Macro.throwErrorAt body "decl: unexpected arm body"

partial def elabUBlk (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `ublk) : MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(ublk| let $x:ident = $e:uterm ; $rest:ublk) => do
    let (e', n1) ← elabUTerm rctx pctx next e
    let name := x.getId.toString
    let (rest', n2) ← elabUBlk ((name, n1) :: rctx) pctx (n1 + 1) rest
    return (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩ $e' $rest'), n2)
  | `(ublk| $p:uterm := $e:uterm ; $rest:ublk) => do
    let (p', n1) ← elabUTerm rctx pctx next p
    let (e', n2) ← elabUTerm rctx pctx n1 e
    let (rest', n3) ← elabUBlk rctx pctx n2 rest
    return (← `(Dllbc.Term.assign $p' $e' $rest'), n3)
  | `(ublk| $e:uterm ; $rest:ublk) => do
    let (e', n1) ← elabUTerm rctx pctx next e
    let (rest', n2) ← elabUBlk rctx pctx n1 rest
    return (← `(Dllbc.Term.seq $e' $rest'), n2)
  | `(ublk| $e:uterm) => elabUTerm rctx pctx next e
  | _ => Macro.throwErrorAt stx "decl: unexpected block syntax"

end

end DeclMacro

/-! ## The `decl{ … }` declaration surface -/

declare_syntax_cat declParam
declare_syntax_cat declBody

syntax ident ":" dty : declParam
syntax "{" ublk "}" : declBody              -- body: the unified `uterm`/`ublk` grammar
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
  let bodyT ← match body with                               -- unified `ublk` block, or a `%` splice
    | `(declBody| { $b:ublk }) => do let (t, _) ← elabUBlk fullRctx [] n b; pure t
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
