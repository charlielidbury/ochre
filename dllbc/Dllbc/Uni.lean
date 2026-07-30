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

/-! ## The unified `uterm` / `ublk` grammar (§ phase-3 point 1 — ONE term grammar)

A single expression grammar spanning BOTH fragments, elaborated by `elabU` under a
**mode flag** that is precisely "is this position consumed by ⇒ or ⇝" (the
arrows-decide-fragments thesis at elaboration level):

  * **term mode** (⇒, a runtime position — `decl{}` body, `dllbc{}`): `&mut e` is
    the borrow *operation* (`.borrow`); `let x = e ; …` mints a fresh runtime id
    (`.letIn`); assignment/sequencing/match/call are available.
  * **type mode** (⇝, a comptime position — `decl{}` telescope/retType/back,
    `pure{}`): `&mut τ` / `&mut (s : τ ~> S)` is the borrow *type* (`.borrowT`, the
    snapshot `s` bound as pure var 0 in `S`); `let x = e ; …` is a β-redex
    (de Bruijn). The runtime-only forms are simply not written there.

Forms shared by both modes: application spines, λ/Π/Σ/→/Id/`Type`, `*e`, `Id`,
constructor/const/lemma references. `ublk` is the statement layer (term mode).

**The one disambiguation rule (§ point 2):** `f(a, b)` — an identifier with a
**no-whitespace** paren argument list — is a runtime **call** (lowercase head) or
**ctorApp** (uppercase). Space-separated **juxtaposition** `f a b` (incl.
`f (a) b`) is **pure application** (`ctorApp` when the head is a known ctor). So
`nth(&mut *tl, k, p)` is a call, `botElim Unit p` and `le_rw_r (S x) y` are
application spines, `S(*l)` / `S *l` both mean `ctorApp "S" [*l]`. -/

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
syntax:max "old" "*" uterm:max : uterm                      -- §5.4 old *v: entry snapshot of a borrow-param deref
syntax:max "Id" uterm:max uterm:max uterm:max : uterm        -- Id A a b
syntax:max ident noWs "(" uterm,* ")" : uterm                -- call / ctorApp (NO space before `(`)
syntax:70 "&mut" uterm:65 : uterm                            -- &mut e : borrow (term) / borrowT (type)
syntax:70 "&mut" "(" uterm "~>" uterm ")" : uterm            -- borrow type &mut (τ ↝ S)
syntax:70 "&mut" "(" ident ":" uterm "~>" uterm ")" : uterm  -- borrow type &mut (s : τ ↝ S)
syntax:65 uterm:65 uterm:66 : uterm                          -- application (juxtaposition)
syntax:10 "λ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- lambda
syntax:10 "Π" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Pi
syntax:10 "Σ" "(" ident ":" uterm ")" "→" uterm:10 : uterm   -- Sigma (arrow form)
syntax:10 "Σ" "(" ident ":" uterm ")" "." uterm:10 : uterm   -- Sigma (dot form)
syntax:10 uterm:11 "→" uterm:10 : uterm                      -- non-dependent arrow
syntax:max "match" ident "{" uarm,* "}" : uterm              -- runtime match (§3)
syntax:max "if" uterm "{" ublk "}" "else" "{" ublk "}" : uterm  -- §12 sugar over a Bool match

-- Pure eliminator sugar (§15b) — for `pure{}` / comptime positions. Arm bodies are
-- `ublk` so a `let x = e ; …` proof-let sequence (StdLemmas) works uniformly.
declare_syntax_cat uelimArm
syntax ident ("(" ident ")")* (ident)? "=>" ublk : uelimArm
syntax:max "elim" uterm:max "return" uterm:max "{" uelimArm,* "}" : uterm
syntax:max "elim" uterm:max "generalizing" uterm:max "{" uelimArm,* "}" : uterm

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
def constSet : List String := ["Nat", "Bool", "List", "Bot", "Unit", "natRec", "boolRec", "listRec", "sigmaRec", "botElim", "j", "k"]
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

partial def elabUTerm (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `uterm) : MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(uterm| ()) => return (← `(Dllbc.Term.unit), next)
  | `(uterm| ($e:uterm)) => elabUTerm isTy rctx pctx next e
  | `(uterm| Type) => return (← `(Dllbc.Term.type), next)
  | `(uterm| % $e:term) => return (← `(($e : Dllbc.Term)), next)
  | `(uterm| $n:num) => return (← Dllbc.Macro.buildNat n.getNat, next)
  | `(uterm| old * $e:uterm) => do
    -- §5.4 `old *v`: the ENTRY snapshot, sugar over the telescope's existing
    -- payload snapshot. Elaborates to `@old(*v)`; `markExit` strips the marker to
    -- a plain `*v` read at seed (entry), so it never reaches the kernel.
    let (e', n) ← elabUTerm isTy rctx pctx next e
    return (← `(Dllbc.Term.app (Dllbc.Term.const "old") (Dllbc.Term.deref $e')), n)
  | `(uterm| * $e:uterm) => do
    let (e', n) ← elabUTerm isTy rctx pctx next e
    return (← `(Dllbc.Term.deref $e'), n)
  | `(uterm| &mut ( $x:ident : $τ:uterm ~> $s:uterm )) => do     -- borrow type, snapshot binder
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (s', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 s
    return (← `(Dllbc.Term.borrowT $τ' $s'), n2)
  | `(uterm| &mut ( $τ:uterm ~> $s:uterm )) => do                -- borrow type, S ignores s
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (s', n2) ← elabUTerm isTy rctx pctx n1 s
    return (← `(Dllbc.Term.borrowT $τ' (Dllbc.Term.shiftPure 1 0 $s')), n2)
  | `(uterm| &mut $e:uterm) => do                                -- mode-decided: borrowT vs borrow
    let (e', n) ← elabUTerm isTy rctx pctx next e
    if isTy then return (← `(Dllbc.Term.borrowT $e' (Dllbc.Term.shiftPure 1 0 $e')), n)
    else return (← `(Dllbc.Term.borrow $e'), n)
  | `(uterm| Id $a:uterm $b:uterm $c:uterm) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (b', n2) ← elabUTerm isTy rctx pctx n1 b
    let (c', n3) ← elabUTerm isTy rctx pctx n2 c
    return (← `(Dllbc.Term.idT $a' $b' $c'), n3)
  | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => do
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.lam $τ' $b'), n2)
  | `(uterm| Π ($x:ident : $τ:uterm) → $b:uterm) => do
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.pi $τ' $b'), n2)
  | `(uterm| Σ ($x:ident : $τ:uterm) → $b:uterm) => do
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $τ' $b'), n2)
  | `(uterm| Σ ($x:ident : $τ:uterm). $b:uterm) => do
    let (τ', n1) ← elabUTerm isTy rctx pctx next τ
    let (b', n2) ← elabUTerm isTy rctx (x.getId.toString :: pctx) n1 b
    return (← `(Dllbc.Term.sigmaT $τ' $b'), n2)
  | `(uterm| $a:uterm → $b:uterm) => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (b', n2) ← elabUTerm isTy rctx ("_" :: pctx) n1 b
    return (← `(Dllbc.Term.pi $a' $b'), n2)
  | `(uterm| $c:ident($args,*)) => do                 -- no-space paren: call / ctorApp
    let (args', n) ← elabUList isTy rctx pctx next args.getElems.toList
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
  | `(uterm| if $c:uterm { $t:ublk } else { $f:ublk }) => do  -- §12 sugar → Bool match
    let (c', n1) ← elabUTerm false rctx pctx next c
    let scrutId := n1
    let (t', n2) ← elabUBlk false rctx pctx (n1 + 1) t
    let (f', n3) ← elabUBlk false rctx pctx n2 f
    return (← `(Dllbc.Term.letIn ⟨$(quote scrutId), "__if"⟩ $c'
      (Dllbc.Term.matchE ⟨$(quote scrutId), "__if"⟩
        [Dllbc.Branch.mk "True" [] $t', Dllbc.Branch.mk "False" [] $f'])), n3)
  | `(uterm| elim $scrut:uterm return $motive:uterm { $arms,* }) =>
    elabUElim isTy rctx pctx next scrut motive arms.getElems
  | `(uterm| elim $scrut:uterm generalizing $goal:uterm { $arms,* }) =>
    elabUGenElim isTy rctx pctx next scrut goal arms.getElems
  | `(uterm| $_:uterm $_:uterm) => do                 -- application spine (juxtaposition)
    let (head, args) := collectAppU stx
    match head with
    | `(uterm| $h:ident) =>
      let hs := h.getId.toString
      let (argTerms, n) ← elabUList isTy rctx pctx next args.toList
      if ctorSet.contains hs && (idxOf? pctx hs).isNone && (rctx.lookup hs).isNone then
        return (← `(Dllbc.Term.ctorApp $(quote hs) [$argTerms,*]), n)
      else
        let hterm ← resolveName rctx pctx h
        let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
        return (out, n)
    | _ => do
      let (hterm, n0) ← elabUTerm isTy rctx pctx next head
      let (argTerms, n) ← elabUList isTy rctx pctx n0 args.toList
      let out ← argTerms.foldlM (fun acc a => `(Dllbc.Term.app $acc $a)) hterm
      return (out, n)
  | `(uterm| $x:ident) => return (← resolveName rctx pctx x, next)
  | _ => Macro.throwErrorAt stx "decl: unexpected term syntax"

partial def elabUList (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat) :
    List (TSyntax `uterm) → MacroM (Array (TSyntax `term) × Nat)
  | [] => pure (#[], next)
  | a :: as => do
    let (a', n1) ← elabUTerm isTy rctx pctx next a
    let (rest, n2) ← elabUList isTy rctx pctx n1 as
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
  | `(uarmBody| { $b:ublk }) => elabUBlk false rctx pctx next b
  | `(uarmBody| $e:uterm) => elabUTerm false rctx pctx next e
  | _ => Macro.throwErrorAt body "decl: unexpected arm body"

partial def elabUBlk (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (stx : TSyntax `ublk) : MacroM (TSyntax `term × Nat) := do
  match stx with
  | `(ublk| let $x:ident = $e:uterm ; $rest:ublk) => do
    let (e', n1) ← elabUTerm isTy rctx pctx next e
    let name := x.getId.toString
    if isTy then                                            -- ⇝: β-redex, `x` a pure de Bruijn binder
      let (rest', n2) ← elabUBlk isTy rctx (name :: pctx) n1 rest
      return (← `(Dllbc.Term.app (Dllbc.Term.lam Dllbc.Term.type $rest') $e'), n2)
    else                                                    -- ⇒: letIn, `x` a fresh runtime slot
      let (rest', n2) ← elabUBlk isTy ((name, n1) :: rctx) pctx (n1 + 1) rest
      return (← `(Dllbc.Term.letIn ⟨$(quote n1), $(quote name)⟩ $e' $rest'), n2)
  | `(ublk| $p:uterm := $e:uterm ; $rest:ublk) => do
    let (p', n1) ← elabUTerm isTy rctx pctx next p
    let (e', n2) ← elabUTerm isTy rctx pctx n1 e
    let (rest', n3) ← elabUBlk isTy rctx pctx n2 rest
    return (← `(Dllbc.Term.assign $p' $e' $rest'), n3)
  | `(ublk| $e:uterm ; $rest:ublk) => do
    let (e', n1) ← elabUTerm isTy rctx pctx next e
    let (rest', n2) ← elabUBlk isTy rctx pctx n1 rest
    return (← `(Dllbc.Term.seq $e' $rest'), n2)
  | `(ublk| $e:uterm) => elabUTerm isTy rctx pctx next e
  | _ => Macro.throwErrorAt stx "decl: unexpected block syntax"

/-- `elim scrut return motive { arms }` → the matching recursor (§15b), ported from
    PureMacro.elabElim over `uterm`. Pure — the arm binders (k/ih/h/t) push `pctx`. -/
partial def elabUElim (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (scrut motive : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : MacroM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm isTy rctx pctx next scrut
  let (motiveT, n2) ← elabUTerm isTy rctx pctx n1 motive
  let motiveBare := match motive with | `(uterm| ($e:uterm)) => e | _ => motive
  let (mName, mTy, mBody) ← match motiveBare with
    | `(uterm| λ ($x:ident : $τ:uterm). $b:uterm) => pure (x.getId.toString, τ, b)
    | _ => Macro.throwError "elim: motive must be a λ `(x : τ). …`"
  let armFor (c : String) : MacroM (Option (Array Ident × Option Ident × TSyntax `ublk)) := do
    for arm in arms do
      match arm with
      | `(uelimArm| $ctor:ident $[($bs:ident)]* $[$ih:ident]? => $body:ublk) =>
        if ctor.getId.toString == c then return some (bs, ih, body)
      | _ => pure ()
    return none
  let getArm (c : String) : MacroM (Array Ident × Option Ident × TSyntax `ublk) := do
    match ← armFor c with
    | some r => pure r
    | none => Macro.throwError s!"elim: missing arm for constructor '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:ublk) => some ctor.getId.toString
    | _ => none)
  let pOf (leading : List String) : MacroM (TSyntax `term) := do
    pure (← elabUTerm isTy rctx (mName :: leading ++ pctx) n2 mBody).1
  if names.contains "Z" || names.contains "S" then
    let (_, _, zb) ← getArm "Z"; let z := (← elabUBlk isTy rctx pctx n2 zb).1
    let (sb, sih, sbody) ← getArm "S"
    let kName := (sb.get! 0).getId.toString
    let ihName := (sih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf []
    let body := (← elabUBlk isTy rctx (ihName :: kName :: pctx) n2 sbody).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "natRec") $motiveT) $z)
        (Dllbc.Term.lam (Dllbc.Term.const "Nat") (Dllbc.Term.lam $ihDom $body))) $scrutT), n2)
  else if names.contains "True" || names.contains "False" then
    let (_, _, tb) ← getArm "True"; let t := (← elabUBlk isTy rctx pctx n2 tb).1
    let (_, _, fb) ← getArm "False"; let f := (← elabUBlk isTy rctx pctx n2 fb).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motiveT) $t) $f) $scrutT), n2)
  else if names.contains "Nil" || names.contains "Cons" then
    let (_, _, nb) ← getArm "Nil"; let n := (← elabUBlk isTy rctx pctx n2 nb).1
    let (cb, cih, cbody) ← getArm "Cons"
    let hName := (cb.get! 0).getId.toString
    let tName := (cb.get! 1).getId.toString
    let ihName := (cih.getD (mkIdent `ih)).getId.toString
    let ihDom ← pOf [hName]
    let body := (← elabUBlk isTy rctx (ihName :: tName :: hName :: pctx) n2 cbody).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "listRec") (Dllbc.Term.const "Nat")) $motiveT) $n)
        (Dllbc.Term.lam (Dllbc.Term.const "Nat") (Dllbc.Term.lam (Dllbc.Term.app (Dllbc.Term.const "List") (Dllbc.Term.const "Nat")) (Dllbc.Term.lam $ihDom $body)))) $scrutT), n2)
  else if names.contains "Pair" then
    -- Σ elimination (§9). `sigmaRec` takes Σ's two parameters — the domain `A` and
    -- the FAMILY `λ x. B` — so the motive's binder type must be written as the Σ
    -- itself, `λ (p : Σ (x : A) → B). goal`. Determined from what is written, never
    -- inferred: a wrong `A`/`B` fails at the use site like every other elim motive.
    -- No `ih`: Σ is not recursive, so the single arm binds exactly the two fields.
    let mTyBare := match mTy with | `(uterm| ($e:uterm)) => e | _ => mTy
    let (aSyn, bName, bSyn) ← match mTyBare with
      | `(uterm| Σ ($y:ident : $A:uterm) → $B:uterm) => pure (A, y.getId.toString, B)
      | `(uterm| Σ ($y:ident : $A:uterm). $B:uterm) => pure (A, y.getId.toString, B)
      | _ => Macro.throwError "elim: a Pair motive's binder type must be written as `Σ (x : A) → B`"
    let aT := (← elabUTerm isTy rctx pctx n2 aSyn).1
    -- `B` under its own binder at position 0 — de Bruijn-correct for BOTH uses (the
    -- family `λ x. B` and the arm's second binder domain), whatever the arm names it.
    let bT := (← elabUTerm isTy rctx (bName :: pctx) n2 bSyn).1
    let (pb, _, pbody) ← getArm "Pair"
    let xName := (pb.get! 0).getId.toString
    let yName := (pb.get! 1).getId.toString
    let body := (← elabUBlk isTy rctx (yName :: xName :: pctx) n2 pbody).1
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "sigmaRec") $aT)
        (Dllbc.Term.lam $aT $bT)) $motiveT)
        (Dllbc.Term.lam $aT (Dllbc.Term.lam $bT $body))) $scrutT), n2)
  else
    Macro.throwError "elim: arms do not match a known recursor (Nat/Bool/List/Σ)"

/-- `elim scrut generalizing goal { arms }` (§18), ported from PureMacro.elabGenElim. -/
partial def elabUGenElim (isTy : Bool) (rctx : List (String × Nat)) (pctx : List String) (next : Nat)
    (scrut goal : TSyntax `uterm) (arms : Array (TSyntax `uelimArm)) : MacroM (TSyntax `term × Nat) := do
  let (scrutT, n1) ← elabUTerm isTy rctx pctx next scrut
  let (goalT, n2) ← elabUTerm isTy rctx pctx n1 goal
  let armBody (c : String) : MacroM (TSyntax `term) := do
    for arm in arms do
      match arm with
      | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $body:ublk) =>
        if ctor.getId.toString == c then return (← elabUBlk isTy rctx pctx n2 body).1
      | _ => pure ()
    Macro.throwError s!"elim generalizing: missing arm '{c}'"
  let names := arms.filterMap (fun a => match a with
    | `(uelimArm| $ctor:ident $[($_:ident)]* $[$_:ident]? => $_:ublk) => some ctor.getId.toString
    | _ => none)
  if names.contains "True" || names.contains "False" then
    let t ← armBody "True"
    let f ← armBody "False"
    let nf := Lean.mkIdent `Dllbc.Std.nfTerm
    let motive ← `(Dllbc.Term.lam (Dllbc.Term.const "Bool")
      (Dllbc.abstractOccurrences ($nf $scrutT) ($nf $goalT)))
    return (← `(Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.app (Dllbc.Term.const "boolRec") $motive) $t) $f) $scrutT), n2)
  else
    Macro.throwError "elim generalizing: only Bool motives supported (§18); Nat/List use the `return` form"

end

/-- Build the telescope entry syntaxes, threading the runtime-var context so that
    parameter `i`'s type sees exactly params `0 .. i-1` (each at its positional
    id) — the `seedTelescope` convention. Types elaborate in type mode (⇝). -/
partial def buildTele (rctx : List (String × Nat)) (i : Nat) :
    List (String × TSyntax `uterm) → MacroM (Array (TSyntax `term))
  | [] => pure #[]
  | (nm, τ) :: rest => do
    let (τT, _) ← elabUTerm true rctx [] 0 τ
    let entry ← `((($(quote nm), $τT) : String × Dllbc.Term))
    let rest' ← buildTele (rctx ++ [(nm, i)]) (i + 1) rest
    pure (#[entry] ++ rest')

end DeclMacro

end Dllbc
