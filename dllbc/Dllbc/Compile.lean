import Dllbc.Syntax
import Dllbc.Value
import Dllbc.Std
import Dllbc.Program

/-!
# `Dllbc.Compile` — the borrow-free fragment, compiled to real Lean functions

**A PROBE (M35), not a kernel component.** Nothing here is imported by
`Dllbc.lean`; the default build is unaffected. What it answers is the user's
question: *can the comptime analysis output something which can then be run —
the λ compiled down to a Lean function, every application site an application of
that function?*

The pipeline is three passes and one command:

  1. **`CTy`** — the target type IR, and `compileTy`, which is **where erasure
     happens**. A DLLBC type either denotes runtime data (`Nat`, `Bool`,
     `List τ`, a Σ of data, a Π between data) or it denotes a *spec* — `Type`
     itself, an `Id`, a `Le`/`Sorted` application, anything whose inhabitants are
     proofs. The second kind compiles to `CTy.erased`, and erasure is then not a
     separate pass at all: a binder whose domain is `erased` is dropped along with
     its argument, a pair whose second component is `erased` is its first
     component, a `let` whose type is `erased` never reaches the output.

  2. **`CExpr`** — the target expression IR: Lean's own λ, application, `let`,
     `match`, constructors, and the three eliminator combinators (`Rt.natrec`,
     `Rt.listrec`, `Rt.boolrec`) that DLLBC's `natRec`/`listRec`/`boolRec` become.

  3. **the renderer** — `CExpr` → Lean source text → `Lean.Parser` → `elabCommand`,
     so `fn Double (n : Nat) -> Nat { … }` really does become a Lean
     `def Double : Nat → Nat`, and `Double(3)` really is `Double 3`.

## What "erasure is type-directed, not mode-directed" means, and why it had to be

The obvious reading of §6's capitalisation convention is that a capital binder is
comptime, comptime means erased, so erasure is a case test on the binder's name.
**That reading is wrong, and the corpus refutes it in one line**: `Std.addFn` is
`λ (A : Nat). λ (B : Nat). natRec …`, both binders capital, and it is the
addition every program computes with. Capitalisation says how an argument is READ
(⇝-snapshot vs ⇒-move); it says nothing about whether the argument is needed to
produce the answer. A proof parameter and a `Nat` parameter are both capital and
only one of them erases.

So the mode discipline is not the safety net for erasure — the TYPE is. What the
mode discipline does buy is the other half of the claim: since a capital binding
is only ever cited from ⇝ positions, a dropped binding cannot be *moved* out of a
slot somewhere downstream, so dropping it cannot leave a hole in Ω. Deletion is
mechanical in that sense. It is not mechanical in the sense of being readable off
the binder.
-/

namespace Dllbc.Compile

/-! ## The target type IR -/

/-- A type in the target language. `erased` is the compile-time-only layer:
    proofs, types, and anything built out of them. -/
inductive CTy where
  | nat | bool | unit
  | list   : CTy → CTy
  | prod   : CTy → CTy → CTy
  | arrow  : CTy → CTy → CTy
  | erased : CTy
deriving BEq, DecidableEq, Repr, Inhabited

/-- Render a `CTy` as Lean source. `erased` has no rendering — every site that
    could produce one is required to have dropped it first. -/
partial def CTy.render : CTy → String
  | .nat => "Nat"
  | .bool => "Bool"
  | .unit => "Unit"
  | .list t => "(List " ++ t.render ++ ")"
  | .prod a b => "(" ++ a.render ++ " × " ++ b.render ++ ")"
  | .arrow a b => "(" ++ a.render ++ " → " ++ b.render ++ ")"
  | .erased => "«erased»"

/-- Is this the compile-time-only layer? -/
def CTy.isErased : CTy → Bool | .erased => true | _ => false

/-! ## `compileTy` — the translation, and therefore the erasure

    ### There is no dependency check here, and that took a bug to learn

    The first version tested `occursP x cod` and erased a Π whose codomain
    mentions its binder, on the reasoning that a dependent function between DATA
    has no target type (there is no `Vec`). It erased the wrong thing
    immediately: `fn Idx (n : Nat, H : Le n n) -> Nat` has a codomain
    `Π (H : Le n n) → Nat` that MENTIONS `n`, so the whole function erased and its
    call site rendered an erased value. The dependency was real and lived
    entirely inside the proof argument, which erasure was about to delete.

    The check is not needed, because `CTy` has no variables: a type that really
    depends on a data value is a former this translation does not have a case for
    (`Array n T` is the only one in the calculus), so it lands in `erased` on its
    own. Dropping the test cannot turn a dependent type into an arrow — it can
    only stop erasure from firing on dependencies that were about to vanish. -/

/-- Translate a DLLBC type to the target. Total: everything that is not data is
    `erased`, which is the honest answer for `Type`, `Id`, `Le a b`, `Sorted l`,
    and every other spec.

    The three structural cases are where erasure does its real work:

      * **Π** — an erased DOMAIN drops the argument (`Π (H : Le a b) → Nat` is
        `Nat`); an erased CODOMAIN erases the whole arrow (a lemma is not code).
      * **Σ** — an erased component is projected away (`Σ (l : List Nat) → Sorted
        l` is `List Nat`), which is exactly how a postcondition-carrying return
        value loses its postcondition.
      * **⇝τ** — the mode marker is dropped. Both modes become ordinary Lean
        arguments; the target has one calling convention. -/
partial def compileTy : Term → CTy
  | .const "Nat" => .nat
  | .const "Bool" => .bool
  | .const "Unit" => .unit
  | .app (.const "List") t =>
    match compileTy t with | .erased => .erased | e => .list e
  | .cmpT t => compileTy t
  | .pi _ d b =>
    match compileTy d, compileTy b with
    | _, .erased => .erased
    | .erased, cb => cb
    | cd, cb => .arrow cd cb
  | .sigmaT _ d b =>
    match compileTy d, compileTy b with
    | .erased, cb => cb
    | cd, .erased => cd
    | cd, cb => .prod cd cb
  | _ => .erased

/-! ## The target runtime: what DLLBC's recursors become

    Lean's own `Nat.rec`/`List.rec` are *recursors*, and the code generator
    refuses them ("code generator does not support recursor"), so a `def` built
    out of them could be checked but never run — and running it is the entire
    point of the differential. These three are the same eliminators written as
    ordinary structural recursion, which the equation compiler turns into real
    code. `natRec P z s n` compiles to `Rt.natrec z s n`, and the arm order is
    DLLBC's own: the step arm takes the predecessor and then the recursive
    result, exactly as `Std.sucArm` is written.

    They are non-dependent, and that is a real restriction with a stated
    boundary: after erasure a motive over DATA is constant in the corpus
    (`countFn`'s is `λ_. Nat`, `takeFn`'s is `λ_. List Nat → List Nat`), and a
    motive that is genuinely dependent in a data-relevant way — `Array n T` — is
    refused by name in `compileRec` rather than mis-compiled. -/
namespace Rt

/-- `natRec` at the target. -/
def natrec {α : Type} (z : α) (s : Nat → α → α) : Nat → α
  | 0 => z
  | n + 1 => s n (natrec z s n)

/-- `listRec` at the target. -/
def listrec {α β : Type} (n : β) (c : α → List α → β → β) : List α → β
  | [] => n
  | h :: t => c h t (listrec n c t)

/-- `boolRec` at the target — true arm first, as DLLBC writes it. -/
def boolrec {α : Type} (t f : α) : Bool → α
  | true => t
  | false => f

end Rt

/-! ## The target expression IR -/

/-- An expression in the target language. `erased` is a value that must never
    reach the output: it is what a proof or a type compiles to, and the renderer
    FAILS on it. That failure is the probe's instrument — every place the
    "comptime deletes mechanically" claim bends shows up as an `erased` in a
    position the renderer needs. -/
inductive CExpr where
  | var    : String → CExpr
  | lam    : String → CTy → CExpr → CExpr
  | app    : CExpr → CExpr → CExpr
  | letE   : String → CExpr → CExpr → CExpr
  | natLit : Nat → CExpr
  | ctorE  : String → List CExpr → CExpr
  | ascribe : CExpr → CTy → CExpr
  /-- Scrutinee, then alternatives as (Lean pattern head, binders, body). -/
  | matchE : CExpr → List (String × List String × CExpr) → CExpr
  | unitE  : CExpr
  | erased : CExpr
deriving Inhabited

/-- Lean keywords a DLLBC binder could legally be spelled as. -/
def leanKeywords : List String :=
  ["fun", "let", "match", "with", "do", "if", "then", "else", "end", "from",
   "have", "show", "in", "at", "by", "where", "deriving", "this", "def",
   "theorem", "open", "namespace", "section", "variable", "instance", "class",
   "structure", "inductive", "set_option", "attribute", "macro", "syntax"]

/-- A DLLBC binder name as a Lean identifier. The reserved `§` namespace (§2.1)
    cannot be written in Lean at all, so it is spelled out; a name that collides
    with a keyword gets a trailing prime. -/
def sanitize (s : String) : String :=
  let s := String.mk (s.data.map (fun c =>
    if c.isAlphanum || c == '_' || c == '\'' then c else '_'))
  let s := if s.isEmpty then "x_" else s
  let s := if (s.get 0).isDigit then "x" ++ s else s
  -- `§_` is the reserved name for a binder nothing refers to (§2.1). Rendering it
  -- as Lean's own `_` rather than as `__` is not cosmetic: two of them can nest
  -- (`eqbFn`'s inner arms have exactly that shape), and `__` would SHADOW where
  -- `_` cannot be referred to at all — so a body that did cite one becomes an
  -- "unknown identifier" at the target instead of a silent capture.
  if s.all (· == '_') then "_"
  else if leanKeywords.contains s then s ++ "'" else s

/-! ## The renderer — `CExpr` to Lean source text

    Source text rather than `Syntax` built by hand, for one reason that matters to
    a probe: the generated program is then a thing you can READ. The command below
    parses this text with Lean's own parser and elaborates the result, so nothing
    is lost by going through a string — an ill-formed rendering is a parse error
    at the command, not a silently wrong `Expr`. -/

/-- Render, or fail naming the position an erased value reached. -/
partial def CExpr.render : CExpr → Except String String
  | .var x => .ok x
  | .lam x τ b => do .ok s!"(fun ({x} : {τ.render}) => {← b.render})"
  | .app f a => do .ok s!"({← f.render} {← a.render})"
  | .letE x v b => do .ok s!"(let {x} := {← v.render};\n{← b.render})"
  | .natLit n => .ok (toString n)
  | .ctorE c [] => .ok c
  | .ctorE c args => do
    let parts ← args.mapM CExpr.render
    .ok ("(" ++ c ++ " " ++ String.intercalate " " parts ++ ")")
  | .ascribe e τ => do .ok s!"(({← e.render}) : {τ.render})"
  | .matchE s alts => do
    let ss ← s.render
    let rendered ← alts.mapM (fun alt => do
      let (pat, bs, body) := alt
      let p := if bs.isEmpty then pat else pat ++ " " ++ String.intercalate " " bs
      .ok s!"  | {p} => {← body.render}")
    .ok ("(match " ++ ss ++ " with\n" ++ String.intercalate "\n" rendered ++ ")")
  | .unitE => .ok "()"
  | .erased =>
    .error "an ERASED value reached a rendered position — erasure and use disagree here"

/-! ## The compiler

    Bidirectional in the small way this fragment needs. `synth` is the whole
    engine — every DLLBC λ is Church-style, so a binder always knows its own
    domain and nothing needs an expected type to be built. `check` exists for the
    two forms that genuinely have none: a bare `Nil` (no element type in the
    syntax) and any term at an erased position (which is answered without looking
    at the term at all).

    The context maps a name to its **DLLBC type**, not to its `CTy`. That is
    deliberate: erasure at an application site is decided by walking the callee's
    Π one binder at a time and asking `compileTy` of each DOMAIN, and a `CTy`
    context would already have collapsed the erased binders away, losing the
    correspondence between the arrows in the type and the arguments in the
    spine. -/

abbrev Ctx := List (String × Term)

/-- The DLLBC types of a constructor's fields at a given result type. -/
def fieldTys (c : String) (ty : Term) : Option (List (String × Term)) :=
  match Pure.ctorSig c with
  | some sig => sig.fieldTypes (Pure.whnf 1000 ty)
  | none => none

/-- The kernel constants that are TYPE FORMERS rather than eliminators. Naming
    a type is naming a value of type `Type`, which erases — so these are the
    constants a program may legally mention in term position. -/
def typeFormers : List String :=
  ["Nat", "Bool", "Unit", "Bot", "List", "Array", "Id", "Type"]

/-- The Lean pattern head, and the DLLBC ctor's target constructor. -/
def targetCtor : String → Option String
  | "Z" => some "Nat.zero" | "S" => some "Nat.succ"
  | "Nil" => some "List.nil" | "Cons" => some "List.cons"
  | "True" => some "Bool.true" | "False" => some "Bool.false"
  | "unit" => some "Unit.unit" | "Pair" => some "Prod.mk"
  | _ => none

/-! ### Head reduction that does NOT normalize

    `Pure.whnf` is `Pure.nf` (the domain split made them the same function), and a
    full normalizer is exactly the wrong tool here: it would take `Π (H : Le 1 2)
    → Nat` to `Π (H : Unit) → Nat`, and `Unit` is DATA. Erasure has to read the
    type as WRITTEN, so the only reduction this compiler does to a type is β at
    the head — enough to expose the Π under `(λ N. Π …) 3`, and nothing more.

    That is not a shortcut, it is the finding: see the file-foot note on
    conversion-stability. -/

/-- One β step at the head of a spine, if there is one. -/
partial def betaStep : Term → Option Term
  | .app (.lam x _ b) a => some (Term.substP x.name a b)
  | .app (.cmpT f) a => betaStep (.app f a)
  | .app f a => (betaStep f).map (.app · a)
  | .cmpT t => (betaStep t).map Term.cmpT
  | _ => none

/-- β-head-normalize, bounded. -/
partial def headNf (fuel : Nat) (t : Term) : Term :=
  match fuel with
  | 0 => t
  | f + 1 => match betaStep t with | some t' => headNf f t' | none => t

/-- Expose a Π, β-reducing the head if need be. `⇝τ` is transparent here: the
    mode marker sits on a domain and is not itself a former. -/
partial def headPi? (fuel : Nat) (t : Term) : Option (String × Term × Term) :=
  match headNf fuel t with
  | .pi x d b => some (x, d, b)
  | .cmpT t' => match t' with | .pi x d b => some (x, d, b) | _ => none
  | _ => none

/-- The head of an application spine and its arguments, left to right. -/
def spineOf : Term → Term × List Term
  | .app f a => let (h, as) := spineOf f; (h, as ++ [a])
  | t => (t, [])

/-- Look a name up in the context, innermost binding first. -/
def lookupCtx (Γ : Ctx) (x : String) : Option Term := Γ.lookup x

/-- The DLLBC `Nat` a constructor chain denotes, for rendering literals. -/
partial def natLitOf? : Term → Option Nat
  | .ctorApp "Z" [] => some 0
  | .ctorApp "S" [t] => (natLitOf? t).map (· + 1)
  | _ => none

/-- The three data type constants, as DLLBC terms. -/
def tNat : Term := .const "Nat"
def tBool : Term := .const "Bool"
def tUnit : Term := .const "Unit"
def tList (a : Term) : Term := .app (.const "List") a

/-! ### `synth` / `check` -/

mutual

/-- Compile a term, returning its target expression and its DLLBC type.

    The wrapper is the erasure rule stated once: **a term whose TYPE erases
    compiles to nothing**, whatever the term is. Without it every spec
    application (`Sorted l`, `Le a b`) would compile its head λ into a real Lean
    function with an `erased` body and the renderer would refuse it. -/
partial def synth (Γ : Ctx) (t : Term) : Except String (CExpr × Term) := do
  let (e, τ) ← synthCore Γ t
  if (compileTy τ).isErased then .ok (.erased, τ) else .ok (e, τ)

/-- The dispatch. -/
partial def synthCore (Γ : Ctx) (t : Term) : Except String (CExpr × Term) := do
  match t with
  | .var x =>
    match lookupCtx Γ x.name with
    | some τ => if (compileTy τ).isErased then .ok (.erased, τ)
                else .ok (.var (sanitize x.name), τ)
    | none => .error s!"unbound runtime variable '{x.name}'"
  | .pvar x =>
    match lookupCtx Γ x with
    | some τ => if (compileTy τ).isErased then .ok (.erased, τ)
                else .ok (.var (sanitize x), τ)
    | none => .error s!"unbound pure variable '{x}'"
  | .unit => .ok (.unitE, tUnit)
  | .type | .pi _ _ _ | .sigmaT _ _ _ | .idT _ _ _ | .borrowT _ _ _ =>
    -- A type in term position. It has type `Type`, which erases.
    .ok (.erased, .type)
  | .cmpT u => synth Γ u
  | .seal _ body ascr => do
    let e ← check Γ ascr body
    .ok (e, ascr)
  | .lam x dom body => do
    let (be, bτ) ← synth ((x.name, dom) :: Γ) body
    let τ := Term.pi x.name dom bτ
    if (compileTy dom).isErased then .ok (be, τ)
    else .ok (.lam (sanitize x.name) (compileTy dom) be, τ)
  | .letIn x rhs rest => do
    let (re, rτ) ← synth Γ rhs
    let (be, bτ) ← synth ((x.name, rτ) :: Γ) rest
    if (compileTy rτ).isErased then .ok (be, bτ)
    else .ok (.letE (sanitize x.name) re be, bτ)
  | .seq a rest => do
    let (ae, aτ) ← synth Γ a
    let (be, bτ) ← synth Γ rest
    if (compileTy aτ).isErased then .ok (be, bτ) else .ok (.letE "_" ae be, bτ)
  | .ctorApp c args => synthCtor Γ c args
  | .matchE x eqn brs => synthMatch Γ x eqn brs
  | .app _ _ => synthSpine Γ t
  | .const c =>
    if typeFormers.contains c then .ok (.erased, .type)
    else .error s!"bare constant '{c}' in term position (a recursor needs its arguments)"
  | .call f _ => .error s!"unresolved call to '{f}' — the surface never bound this name"
  | .borrow _ => .error "BORROW (&m) — outside the borrow-free fragment"
  | .deref _ => .error "DEREF (*) — outside the borrow-free fragment"
  | .assign _ _ _ => .error "ASSIGN (:=) — outside the borrow-free fragment"
  | .index _ _ _ => .error "ARRAY INDEX — outside the borrow-free fragment"
  | .range _ _ _ _ _ _ => .error "ARRAY RANGE (carve) — outside the borrow-free fragment"

/-- Compile a term at a known type. Only two forms need it — the erased layer
    (answered without looking at the term) and a bare `Nil`. -/
partial def check (Γ : Ctx) (τ : Term) (t : Term) : Except String CExpr := do
  if (compileTy τ).isErased then .ok .erased
  else match t with
  | .ctorApp "Nil" [] => .ok (.ascribe (.ctorE "List.nil" []) (compileTy τ))
  | _ => do
    let (e, tτ) ← synth Γ t
    let want := compileTy τ
    let got := compileTy tτ
    if want == got then .ok e
    else .error s!"type mismatch: wanted {want.render}, the term compiles to {got.render}"

/-- Constructors. `Nil` is the one form with no principal type in the syntax; in
    a checked position it takes the expected element type, and the SYNTHESIZING
    fallback here defaults to `List Nat` — the corpus's only element type, and a
    stated approximation rather than an inference. -/
partial def synthCtor (Γ : Ctx) (c : String) (args : List Term) :
    Except String (CExpr × Term) := do
  match c, args with
  | "Z", [] => .ok (.natLit 0, tNat)
  | "S", [a] =>
    match natLitOf? (.ctorApp "S" [a]) with
    | some n => .ok (.natLit n, tNat)
    | none => do let (ae, _) ← synth Γ a; .ok (.ctorE "Nat.succ" [ae], tNat)
  | "True", [] => .ok (.ctorE "Bool.true" [], tBool)
  | "False", [] => .ok (.ctorE "Bool.false" [], tBool)
  | "unit", [] => .ok (.unitE, tUnit)
  | "Nil", [] => .ok (.ascribe (.ctorE "List.nil" []) (.list .nat), tList tNat)
  | "Cons", [h, t] => do
    let (he, hτ) ← synth Γ h
    let te ← check Γ (tList hτ) t
    .ok (.ctorE "List.cons" [he, te], tList hτ)
  | "Pair", [a, b] => do
    let (ae, aτ) ← synth Γ a
    let (be, bτ) ← synth Γ b
    let τ := Term.sigmaT "§_" aτ bτ
    if (compileTy aτ).isErased then .ok (be, τ)
    else if (compileTy bτ).isErased then .ok (ae, τ)
    else .ok (.ctorE "Prod.mk" [ae, be], τ)
  | "Refl", _ => .ok (.erased, .type)
  | "Arr", _ => .error "ARRAY LITERAL — outside the borrow-free fragment"
  | _, _ => .error s!"unknown constructor '{c}'"

/-- A match. One constructor deep, scrutinee a variable (grammar-enforced), field
    types read off `Pure.ctorSig` — the kernel's own table, so the compiler and
    the checker agree about what a branch binds. A field whose type erases
    becomes `_` in the Lean pattern. -/
partial def synthMatch (Γ : Ctx) (x : Var) (eqn : Option Var) (brs : List Branch) :
    Except String (CExpr × Term) := do
  match lookupCtx Γ x.name with
  | none => .error s!"match on unbound scrutinee '{x.name}'"
  | some sτ =>
    let sτ' := headNf 200 sτ
    if (compileTy sτ').isErased then
      .error s!"match on an ERASED scrutinee '{x.name}'"
    else do
      let alts ← brs.mapM (fun br => do
        match fieldTys br.ctor sτ', targetCtor br.ctor with
        | some fts, some pat =>
          if fts.length != br.binders.length then
            .error s!"'{br.ctor}' binds {br.binders.length} fields, its signature has {fts.length}"
          else do
            let binds := br.binders.zip (fts.map Prod.snd)
            let eqnΓ := match eqn with
              | some h => [(h.name, Term.idT tNat .unit .unit)]   -- an `Id`: erased
              | none => []
            let Γ' := (binds.map (fun p => (p.1.name, p.2))) ++ eqnΓ ++ Γ
            let (be, bτ) ← synth Γ' br.body
            let pats := binds.map (fun p =>
              if (compileTy p.2).isErased then "_" else sanitize p.1.name)
            .ok ((pat, pats, be), bτ)
        | none, _ => .error s!"no field signature for '{br.ctor}' at scrutinee type"
        | _, none => .error s!"no target constructor for '{br.ctor}'")
      match alts with
      | [] => .error "empty match (a `Bot` scrutinee — nothing to compile)"
      | (_, τ0) :: _ => .ok (.matchE (.var (sanitize x.name)) (alts.map Prod.fst), τ0)

/-- An application spine. Two jobs: recognize the three recursors at their full
    arity, and — for everything else — walk the head's Π ONE BINDER AT A TIME,
    dropping the argument at each binder whose domain erases. That walk is the
    reason the context carries DLLBC types rather than `CTy`s: `compileTy` of a
    signature has already collapsed the erased arrows away, so it can no longer
    say which of the spine's arguments to drop. -/
partial def synthSpine (Γ : Ctx) (t : Term) : Except String (CExpr × Term) := do
  let (h, args) := spineOf t
  match h, args with
  | .const "natRec", [P, z, s, n] => compileNatRec Γ P z s n
  | .const "listRec", [A, P, pn, pc, l] => compileListRec Γ A P pn pc l
  | .const "boolRec", [P, tb, fb, b] => compileBoolRec Γ P tb fb b
  | .const "j", _ => .ok (.erased, .type)         -- the Id eliminator: proofs only
  | .const c, _ =>
    -- A type former applied to its parameters is a TYPE, and a type in term
    -- position has type `Type`, which erases. `List Nat` reaches here whenever a
    -- program names it as a value (`let T = List Nat`).
    if typeFormers.contains c then .ok (.erased, .type)
    else .error s!"constant '{c}' applied to {args.length} arguments — no compilation rule"
  | _, _ => do
    let (he, hτ) ← synth Γ h
    args.foldlM (fun (acc : CExpr × Term) (a : Term) => do
      let (fe, fτ) := acc
      match headPi? 200 fτ with
      | none => .error "applying a term whose type is not a Π"
      | some (x, d, b) =>
        let resτ := Term.substP x a b
        if (compileTy d).isErased then .ok (fe, resτ)
        else do let ae ← check Γ d a; .ok (.app fe ae, resτ)) (he, hτ)

/-- `natRec P z s n` → `Rt.natrec z s n`. The motive is applied and β-reduced at
    `Z` and at `S Z`; if the two disagree at the target the motive is genuinely
    data-dependent, which is the `Vec`/`Array` wall and is refused by name. -/
partial def compileNatRec (Γ : Ctx) (P z s n : Term) : Except String (CExpr × Term) := do
  let resτ := headNf 200 (.app P n)
  if (compileTy resτ).isErased then .ok (.erased, resτ) else do
    let τ0 := headNf 200 (.app P (.ctorApp "Z" []))
    let τ1 := headNf 200 (.app P (.ctorApp "S" [.ctorApp "Z" []]))
    if compileTy τ0 != compileTy τ1 then
      .error "natRec with a DATA-DEPENDENT motive — the target has no `Vec`"
    else do
      let ze ← check Γ τ0 z
      let se ← check Γ (Term.pi "§k" tNat (Term.pi "§ih" τ0 τ0)) s
      let ne ← check Γ tNat n
      .ok (.app (.app (.app (.var "Dllbc.Compile.Rt.natrec") ze) se) ne, resτ)

/-- `listRec A P pn pc l` → `Rt.listrec pn pc l`. -/
partial def compileListRec (Γ : Ctx) (A P pn pc l : Term) :
    Except String (CExpr × Term) := do
  let resτ := headNf 200 (.app P l)
  if (compileTy resτ).isErased then .ok (.erased, resτ) else do
    let τ0 := headNf 200 (.app P (.ctorApp "Nil" []))
    let τ1 := headNf 200 (.app P (.ctorApp "Cons" [.pvar "§x", .ctorApp "Nil" []]))
    if compileTy τ0 != compileTy τ1 then
      .error "listRec with a DATA-DEPENDENT motive — the target has no `Vec`"
    else do
      let ne ← check Γ τ0 pn
      let ce ← check Γ (Term.pi "§h" A (Term.pi "§t" (tList A) (Term.pi "§ih" τ0 τ0))) pc
      let le ← check Γ (tList A) l
      .ok (.app (.app (.app (.var "Dllbc.Compile.Rt.listrec") ne) ce) le, resτ)

/-- `boolRec P t f b` → `Rt.boolrec t f b` (true arm first, as DLLBC writes it). -/
partial def compileBoolRec (Γ : Ctx) (P tb fb b : Term) :
    Except String (CExpr × Term) := do
  let resτ := headNf 200 (.app P b)
  if (compileTy resτ).isErased then .ok (.erased, resτ) else do
    let τT := headNf 200 (.app P (.ctorApp "True" []))
    let τF := headNf 200 (.app P (.ctorApp "False" []))
    if compileTy τT != compileTy τF then
      .error "boolRec with a DATA-DEPENDENT motive — the target has no dependent `if`"
    else do
      let te ← check Γ τT tb
      let fe ← check Γ τF fb
      let be ← check Γ tBool b
      .ok (.app (.app (.app (.var "Dllbc.Compile.Rt.boolrec") te) fe) be, resτ)

end

/-! ## Programs: the top-level let-chain becomes top-level `def`s

    §8 says a program is a let-chain and a tail, and that is exactly the shape of
    a Lean module: every KEPT top-level binding becomes a `def`, and the tail
    becomes `def main`.

    **Every kept binding, not only the functions**, and the reason is the capture
    rule. A λ may capture a capital binding (`let K = 3; fn F (n) { Add n K }`)
    and may not capture a lowercase one (`S26Prog`'s `a2cap` is the rejection).
    So a function's body can cite an earlier top-level DATA binding — and if that
    binding stayed inside `main` the emitted `def F` would have a free variable.
    Hoisting all of them is one rule instead of two and cannot get that wrong. -/

/-- One emitted Lean definition. -/
structure CDef where
  name : String
  ty   : CTy
  body : CExpr
deriving Inhabited

/-- The whole program: the defs its bindings become, and the tail. -/
structure CProgram where
  defs : List CDef
  main : CExpr
  mainTy : CTy
deriving Inhabited

/-- Walk the top-level let-chain. Erased bindings never reach the output; kept
    ones are hoisted in program order, so a later one may cite an earlier one by
    name exactly as the DLLBC program did. -/
partial def compileProgramGo (Γ : Ctx) (acc : List CDef) :
    Term → Except String CProgram
  | .letIn x rhs rest => do
    let (re, rτ) ← synth Γ rhs
    let Γ' := (x.name, rτ) :: Γ
    let cty := compileTy rτ
    if cty.isErased then compileProgramGo Γ' acc rest
    else compileProgramGo Γ' (acc ++ [⟨sanitize x.name, cty, re⟩]) rest
  | t => do
    let (e, τ) ← synth Γ t
    .ok ⟨acc, e, compileTy τ⟩

/-- Compile a DLLBC program. -/
def compileProgram (t : Term) : Except String CProgram := compileProgramGo [] [] t

/-! ## Rendering a whole program as Lean source -/

/-- One `def`, as source. -/
def CDef.render (d : CDef) : Except String String := do
  .ok s!"def {d.name} : {d.ty.render} :=\n  {← d.body.render}"

/-- The program, as a list of Lean commands: a namespace, the defs, the main, an
    end. Returned as separate strings because `Lean.Parser.runParserCategory`
    parses one command at a time. -/
def CProgram.renderCommands (p : CProgram) (ns : String) : Except String (List String) := do
  let ds ← p.defs.mapM CDef.render
  let m ← p.main.render
  .ok (["namespace " ++ ns] ++ ds
        ++ [s!"def main : {p.mainTy.render} :=\n  {m}", "end " ++ ns])

/-- The program as one readable blob — what the probe prints. -/
def CProgram.renderSource (p : CProgram) (ns : String) : Except String String := do
  .ok (String.intercalate "\n\n" (← p.renderCommands ns))

/-- **The program as ONE expression** — the hoisted defs folded back into nested
    `let`s. Needed for the bulk differential, where 45 generated programs have to
    become 45 definitions with predictable names rather than 45 namespaces; a
    `def` per program is what a list of them can be assembled from. Folding right
    keeps program order, so a later binding still sees the earlier ones. -/
def CProgram.mono (p : CProgram) : CExpr :=
  p.defs.foldr (fun d acc => .letE d.name d.body acc) p.main

/-! ## The borrow-free predicate — what this compiler's domain IS

    Stated on the syntax rather than on the compiler's success, so that "how much
    of the corpus is in the fragment" is a question with an answer independent of
    how good the compiler happens to be. The five forms are §0's ownership
    machinery and ¶2.1's array steps; a term free of them is a term the two
    machines agree about without any loan ever existing. -/
partial def borrowFree : Term → Bool
  | .borrow _ | .deref _ | .assign _ _ _ => false
  | .index _ _ _ | .range _ _ _ _ _ _ => false
  | .borrowT _ _ _ => false
  | .letIn _ r b | .seq r b => borrowFree r && borrowFree b
  | .ctorApp _ args | .call _ args => args.all borrowFree
  | .matchE _ _ brs => brs.all (fun b => borrowFree b.body)
  | .seal _ t u => borrowFree t && borrowFree u
  | .lam _ d b | .pi _ d b | .sigmaT _ d b => borrowFree d && borrowFree b
  | .app f a => borrowFree f && borrowFree a
  | .idT a b c => borrowFree a && borrowFree b && borrowFree c
  | .cmpT t => borrowFree t
  | .var _ | .pvar _ | .type | .const _ | .unit => true

/-! ## Reification — how a compiled value is compared with what DLLBC ran to

    `runProgram` returns an `Env`, a list of `(name, Val)`. The differential asks
    whether the Lean value a compiled `def` holds IS the `Val` the DLLBC machine
    left in that slot, so the compiled side needs a way back into `Val`. -/

/-- A target type whose values can be read back as DLLBC store values. -/
class Reify (α : Type) where
  reify : α → Val

instance : Reify Nat := ⟨Val.nat⟩
instance : Reify Bool := ⟨fun b => Val.ctor (if b then "True" else "False") []⟩
instance : Reify Unit := ⟨fun _ => Val.ctor "unit" []⟩
instance {α : Type} [Reify α] : Reify (List α) :=
  ⟨fun l => l.foldr (fun a acc => Val.cons (Reify.reify a) acc) Val.nil⟩
instance {α β : Type} [Reify α] [Reify β] : Reify (α × β) :=
  ⟨fun p => Val.ctor "Pair" [Reify.reify p.1, Reify.reify p.2]⟩

/-- **The differential, as one function**: DLLBC ran this program; the compiled
    `def` named `slot` holds this Lean value; are they the same value? -/
def agreesAt {α : Type} [Reify α] (t : Term) (slot : String) (v : α) : Bool :=
  match Dllbc.runProgram t with
  | .error _ => false
  | .ok env => match env.lookup slot with
    | some w => w == Reify.reify v
    | none => false

end Dllbc.Compile
