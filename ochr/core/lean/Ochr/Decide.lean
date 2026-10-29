import Ochr.Located

/-!
# Decisions: declared types, and everything decided from them (paper §6.3)

The two evaluation paths (a definition's generic call, where calls and matches on abstract
values close off, and each instance, where they run) must take the same decisions, so no
decision that changes a result is read from a normal form. Every decision of that kind is
made here, from syntax, declarations and declared types: whether a term is erased and
whether it is a proof, a function type's class, which parameters are proofs, [Close]'s row,
whether a match is on a proof, the sort of a type.

This module sits before `Ochr.Machine` in the import graph and does not import it: the
evaluator is not in scope here, so nothing in this file can run a term. What it reads is
syntax, the declarations, the state's tables (`Δ`, the signature, the declared reading
stored with each binding) and the *heads* of values passed to it: an inductive type's
declared sort, a Π-closure's codomain term (D54), a global's declared type, an abstract
value's `Δ` type, a sealed program's head call's declared codomain. Those are the same at
the generic call and at every instance, because evaluation preserves declared types (D55)
and refinement does not change a type's sort (`notes/two-paths-census.md`).

The value-dependent rules that legitimately live in the machine ([Split], `Eq`, conversion,
[Rec], footprints, copy-ness, the dependent-field checks) are listed with their stability
arguments in `notes/two-paths-census.md`.
-/

namespace Ochr

/-- What a call's result type is, for [Close]'s table and for P5. -/
inductive Kind where
  | prop | unit | ref | data
deriving BEq, Inhabited

/-- A syntactic guess at whether a type term denotes a proposition. -/
def isPropTerm? : Term → Option Bool
  | .id .. | .eq .. => some true
  | .nat | .unit | .ref _ | .tind "Pair" _ | .sort _ => some false
  | .pi _ _ c => isPropTerm? c
  | _ => none
termination_by structural t => t

def syntacticKind? : Term → Option Kind
  | .unit => some .unit
  | .ref _ => some .ref
  | t => (isPropTerm? t).map fun b => if b then .prop else .data

/-- Is this term literally the sort `Prop`? -/
def isPropSort : Term → Bool
  | .sort 0 | .val (.sort 0) => true
  | _ => false

/-- Is a declared field type a proposition, read off the declaration: a parameter
declared `: Prop`, or a Prop inductive. -/
def fieldTermIsProp (d : IndDecl) (FT : Term) : M Bool := do
  match FT with
  | .place (.var j) => pure (j < d.params.length && isPropSort (d.params[d.params.length - 1 - j]!).2)
  | .tind m _ => pure ((← lookupInd m).sort == 0)
  -- D71: an equation field is a proof field
  | .eq _ _ _ => pure true
  -- K4: a call of a function declared to return `Prop` (a proof field, `h : Sorted(xs)`)
  | .call (.const f) _ _ => match (← get).globals.find? (·.name == f) with
    | some g => pure (g.ty matches .tPi _ (.pi _ _ (.sort 0)))
    | none => pure false
  | _ => pure false

/-- A field place is a proof iff its declared type is a proposition (syntactic, D42). -/
def fieldIsProof (g : FieldRef) : M Bool := do
  let d ← lookupInd g.ty
  match d.ctors[g.ctor]? with
  | some (_, fields) => match fields[g.idx]? with
    | some (_, FT) => fieldTermIsProp d FT
    | none => pure false
  | none => pure false

/-- D42 (v2.0): a constructor application of a Prop inductive is a proof, erased. -/
def ctorIsProof (ty : String) : M Bool := do
  pure ((← lookupInd ty).sort == 0)

/-- D45: large elimination (a match on a proof producing a non-proof) is allowed only
from a subsingleton: zero constructors, or one whose fields are all propositions. -/
def largeElim (d : IndDecl) : M Bool := do
  match d.ctors with
  | [] => pure true
  | [(_, fields)] => fields.allM fun (_, FT) => fieldTermIsProp d FT
  | _ => pure false

/-- The error of a large elimination from a proof of a non-subsingleton (D45). -/
def subsingletonMsg (d : IndDecl) : String :=
  let why := if d.ctors.length ≥ 2 then s!"it has {d.ctors.length} constructors"
    else "its constructor has a field that is not a proposition"
  s!"[D45] a match on a proof of {d.name} returns a non-proof, but {d.name} is not a subsingleton ({why}): large elimination would tell apart proofs that proof irrelevance identifies"

/-- D45: the match `match p { … }` on constructors of `ty` (or with no arms) is by type. -/
def byTypeMatch (ty : String) (arms : List (Hint × Term)) : M Bool := do
  if arms.isEmpty then return true
  pure ((← lookupInd ty).sort == 0)

/-- What the declared type of a place says: a variable's, through a borrow the borrowed
type's, a constructor field's (a proof field is a proof). -/
def placeDecl (sc : List DeclInfo) : Place → M DeclInfo
  | .var i => do
    if h : i < sc.length then return sc[i]
    if (← get).liveScope then liveDecl (i - sc.length) else pure .other
  | .deref q => do
    match ← placeDecl sc q with
    | .ref d => pure d
    | _ => pure .other
  | .field g _ => do pure (if ← fieldIsProof g then .prop else .other)
  | _ => pure .other

/-- Arms agree on what their declared type says (`any`, a zero-arm match, agrees with all).
Arms that are all proofs agree on a proof, whatever their shapes (a proof variable in one
arm, a function into proofs in another: applied, either is a proof). Arms of which some are
proofs and some not have no common declared type (`conflict`, D63): the paper's "a match has
each arm's" declared type is then undefined, and the match is rejected wherever its declared
type is read ([Type-pos], the erasure pre-pass). -/
def agreeDecl (ds : List DeclInfo) : DeclInfo :=
  if ds.contains .conflict then .conflict else
  match ds.filter (· != .any) with
  | [] => .any
  | d :: rest =>
    if rest.all (· == d) then d
    else if (d :: rest).all DeclInfo.isProof then .prop
    else if (d :: rest).any DeclInfo.isProof then .conflict
    else .other

/-- D77: the arms of a match that computes a type agree on what that type says. Equal readings
agree, and so do arms that are all proofs. Arms that differ while one of them is a Π-type do
not: a binding of such a type would take its erasure class, or whether its calls return a
borrow ([Close]'s row), from whichever arm a computation picks, which the two evaluation paths
need not agree on (`notes/stability.md`, site 7). That is a `conflict`, rejected where a binding
takes the type (`refineDecl`). Anything else is `other`. -/
def agreeTypeDecl (ds : List DeclInfo) : DeclInfo :=
  if ds.contains .conflict then .conflict else
  match ds.filter (· != .any) with
  | [] => .any
  | d :: rest =>
    if rest.all (· == d) then d
    else if (d :: rest).all DeclInfo.isProof then .prop
    else if (d :: rest).any (· matches .pi _) then .conflict
    else .other

/-- The error for a term with no declared type (D63). -/
def conflictMsg (t : Term) (ns : List String) : String :=
  s!"[D63] the arms of a match in {t.pp ns} disagree about being proofs (some are, some are not), so it has no declared type"

/-- The erasure pre-pass: whether a term is erased and whether it is a proof, decided
before it runs, from declared types. A proof is a term whose declared type is a
proposition; a call returning types is erased too (its context is not: D35). -/
def preFlags (t : Term) (d : DeclInfo) : M (Option (Bool × Bool)) := do
  if d == .conflict then err (conflictMsg t [])
  if d == .any then return none
  let p := d.isProof
  -- a stuck block's function (codomain the match's type, `.val B`) is a match: erased iff
  -- it is a proof, like any sequencing form (D35)
  let block := match t with
    | .call (.fix _ _ _ (.val _) _ _) _ _ | .call (.val (.clo _ (.fix _ _ _ (.val _) _ _))) _ _ => true
    | _ => false
  let e := p || (t matches .call ..) && !block && (d matches .sort _)
  pure (some (e, p))

/-- The sort of a sealed program that is a type (v1.4: "a sealed program of sort Prop is
a type"), read off its head call: in result form `L; C`, when the callee's codomain is a
sort. -/
def sealedSort? (t : Term) : M (Option Nat) := do
  let rec body : Term → Term
    | .letIn _ _ u => body u
    | u => u
  match body t with
  | .call (.val f) _ true =>
    let piTy ← match f with
      | .gfn n => pure (some (← lookupGlobal n).ty)
      | .clo cs (.fix _ hs ds c _ _) => pure (some (Value.tPi cs (.pi hs ds c)))
      | .abs σ => pure (some (← absType σ))
      | _ => pure none
    match piTy with
    | some (.tPi _ (.pi _ _ (.sort l))) => pure (some l)
    | some (.tPi _ (.pi _ _ (.val (.sort l)))) => pure (some l)
    | _ => pure none
  | _ => pure none

/-- A fresh abstract value of type `T`, in η-normal form: at `Unit`, `()` (D59 refined: the
readback at type `Unit` is `()`; a value of `Unit` carries nothing). -/
def absOf (T : Value) : M Value := do
  if T == .tUnit then return .unit
  pure (.abs (← freshAbs T))

-- the declared-type readers are mutually recursive, on fuel (all checker code is total)
mutual

/-- D66: `&A` is well formed iff `A : Type₀`. With `Prop : Type₁`, everything in `Type₀` exists
at runtime: data types, function types into data or functions, a type parameter declared in
`Type₀`. Propositions (`P : Prop`), `Prop` and the universes are not in it. The sort is read off
the type (a stuck type's by its head's declared codomain); a type whose sort cannot be read is
not known to be in `Type₀` (fail-safe), and neither is a borrow type (no borrows of borrows). -/
def isBorrowable (fuel : Nat) (T : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if T.typeHasRef then return false
  pure ((← sortOf? fuel' T) == some 1)

/-- The universe level of a type value (`0` is `Prop`), or `none` when the value is not known
to be a type: an abstract value whose type is not a sort, a sealed program whose head call's
codomain is not a sort, any other value. A total query. -/
def sortOf? (fuel : Nat) (T : Value) : M (Option Nat) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match T with
  | .abs σ => match ← absType σ with
    | .sort l => pure (some l)
    | _ => pure none
  | .sealed t => sealedSort? t
  | .tNat | .tUnit | .tRef _ | .tInd .. | .tEq .. | .sort _ | .tPi .. => some <$> sortOf fuel' T
  | _ => pure none

/-- The universe level of a type value: `0` is `Prop`. -/
def sortOf (fuel : Nat) (T : Value) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match T with
  | .tNat | .tUnit | .tRef _ => pure 1
  | .tInd n _ => pure (← lookupInd n).sort
  | .tEq .. => pure 0
  | .sort l => pure (sortSucc l)
  | .abs σ => match ← absType σ with
    | .sort l => pure l
    | S => err s!"σ{σ} : {S} is not a type"
  | .sealed t => match ← sealedSort? t with
    | some l => pure l
    | none => err s!"{T} is not known to be a type"
  | .tPi cs (.pi hs ds c) => do
    -- D55: a type's declared sort is its computed sort, so a Π-type's sort is read off its
    -- parameter and codomain terms, each in the scope of the captured values and the earlier
    -- parameters, never by evaluating them (nothing in this module can run a term)
    let capSc ← cs.reverse.mapM (valueDecl fuel')
    let mut sc := capSc
    let mut ns : List String := cs.map fun _ => "κ"
    let mut l := 0
    for (h, d) in hs.zip ds do
      l := max l (← declSort fuel' sc ns d)
      sc := (← typeDecl fuel' false sc ns d) :: sc
      ns := h.name :: ns
    let lb ← declSort fuel' sc ns c
    pure (if lb == 0 then 0 else max l lb)
  | _ => err s!"{T} is not a type"
termination_by structural fuel

/-- The sort of a type term, read off its declared type (D55): the level `l` when the term's
declared type is the sort `Type_l` (`0` is `Prop`). A term whose declared type is not known
(a hole) is taken to be data (level `1`), as `typePos` takes it. -/
def declSort (fuel : Nat) (sc : List DeclInfo) (ns : List String) (T : Term) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← declOf fuel' false sc ns T with
  | .sort l => pure l
  | .any => pure 1
  | _ => err s!"{T.pp ns} is not a type: its declared type is not a sort"
termination_by structural fuel

-- ### Declared types (D55) and the erasure pre-pass

/-- The declared type of a term, read from the declared types of its heads without
normalising (the D35 notion), in a scope saying what each variable's declared type says
(de Bruijn order; `ns` names them, for messages). With `chk`, every type position inside
the term is checked to have a sort as its declared type (D55); without, only the spine
that decides the result is read (the pre-pass at evaluation). -/
def declOf (fuel : Nat) (chk : Bool) (sc : List DeclInfo) (ns : List String) (t : Term) : M DeclInfo := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let sub (u : Term) : M Unit := if chk then discard (declOf fuel' chk sc ns u) else pure ()
  match t with
  | .place p => placeDecl sc p
  | .borrow p => pure (.ref (← placeDecl sc p))
  | .zero | .tt => pure .other
  | .assign _ u | .succ u | .fst u | .snd u => sub u; pure .other
  | .letIn h u w => do
    let d ← declOf fuel' chk sc ns u
    declOf fuel' chk (d :: sc) (h.name :: ns) w
  | .seq u w => sub u; declOf fuel' chk sc ns w
  | .matchNat _ z s =>
    let d := agreeDecl [← declOf fuel' chk sc ns z, ← declOf fuel' chk sc ns s]
    -- D63: checked where it is written, so that no accepted definition meets it at runtime
    -- (a dead arm is not typed, but the machine reads every term's declared type)
    if chk && d == .conflict then err (conflictMsg t ns)
    pure d
  | .matchInd _ _ arms =>
    let d := agreeDecl (← arms.mapM fun (_, a) => declOf fuel' chk sc ns a)
    if chk && d == .conflict then err (conflictMsg t ns)
    pure d
  | .const n =>     -- an unknown name is the machine's error, reported where it is met
    if let some d := (← get).constDecls.lookup n then return d
    let some g := (← get).globals.find? (·.name == n) | return .any
    let d ← valTypeDecl fuel' g.ty
    modify fun s => { s with constDecls := (n, d) :: s.constDecls }
    pure d
  | .val v => valueDecl fuel' v
  | .sort l => pure (.sort (sortSucc l))
  | .nat | .unit => pure (.sort 1)
  | .ref A => discard (typePos fuel' chk sc ns A); pure (.sort 1)
  | .pi hs ds c => do
    let (sc', ns', l) ← telescope fuel' chk sc ns hs ds
    let lc ← typePos fuel' chk sc' ns' c
    pure (.sort (if lc == 0 then 0 else max l lc))
  | .fix self hs ds c _ body => do
    let (sc', ns', _) ← telescope fuel' chk sc ns hs ds
    discard (typePos fuel' chk sc' ns' c)
    let cd ← typeDecl fuel' chk sc' ns' c
    if chk then
      -- the body sees the parameters, then `self`, then the enclosing scope
      let k := ds.length
      discard (declOf fuel' chk (sc'.take k ++ (DeclInfo.pi cd :: sc)) (ns'.take k ++ (self.name :: ns)) body)
    pure (.pi cd)
  | .call f as _ => do
    let df ← declOf fuel' chk sc ns f
    for a in as do sub a
    pure (match df with
      | .pi r => r
      | .prop => .prop      -- a proof applied is a proof (its type is a Π into a proposition)
      | .any => .any
      | _ => .other)
  | .eq A a b | .id A a b => do
    discard (typePos fuel' chk sc ns A); sub a; sub b; pure (.sort 0)
  | .cong f h => sub f; sub h; pure .prop
  | .ascribe u A => do discard (typePos fuel' chk sc ns A); sub u; typeDecl fuel' chk sc ns A
  | .prim "J" [A, a, b, P, h, u] => do
    discard (typePos fuel' chk sc ns A)
    for x in [a, b, h, u] do sub x
    -- `J(…) : P(b)`, a proposition when `P` returns propositions
    match ← declOf fuel' chk sc ns P with
    | .pi (.sort 0) => pure .prop
    | _ => pure .other
  | .prim "hole" _ => pure .any     -- a hole's type is its context's (docs/07)
  | .prim "trans" as | .prim "symm" as | .prim "rewrite" as | .prim "rewriteR" as =>
    for a in as do sub a
    pure .prop   -- D60: `rewrite h in u` is `J`, a proof
  | .prim "split" [_, u] | .prim "splitArms" [_, u] => declOf fuel' chk sc ns u   -- D61: its body's
  | .prim "clone" [u] => declOf fuel' chk sc ns u
  | .prim _ as => for a in as do sub a
                  pure .other
  | .tind n as => do
    -- D71: an argument at a value parameter is an erased position, not a type position
    let d ← lookupInd n
    for (a, i) in as.zipIdx do
      if d.paramIsType i then discard (typePos fuel' chk sc ns a) else sub a
    pure (.sort d.sort)
  | .ctor ty _ _ ps as => do
    let d ← lookupInd ty
    for (p, i) in ps.zipIdx do
      if d.paramIsType i then discard (typePos fuel' chk sc ns p) else sub p
    for a in as do sub a
    pure (if ← ctorIsProof ty then .prop else .other)
termination_by structural fuel

/-- What a type term says as a declared type: a sort, a Π-type, a borrow type, or a
proposition when its own declared type is `Prop`.

D77: a call of a type function (a global whose declared codomain is a sort), `RefPred(0)`
with `RefPred (n : Nat) : Type₁ := Π(x : &Nat). Prop`, says what its body says as a type,
read from the body's syntax in the scope of the function's declared parameters: a Π-type
term, through `let`s and the arms of a match, which must agree (`agreeTypeDecl`). It used to
read `other`, and the binding's class was then recovered from the evaluated type or the
value (`refineDecl`), which a sealed argument at an instance does not have (stability:
`notes/stability.md`, site 7). The body is read, never run; `vis` stops the unfolding of a
function inside its own body (a recursive type function reads `other` there). -/
def typeDecl (fuel : Nat) (chk : Bool) (sc : List DeclInfo) (ns : List String) (T : Term)
    (vis : List String := []) : M DeclInfo := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- the reading from the term's own declared type: a proposition if its declared sort is `Prop`
  let fallback : M DeclInfo := do
    match ← declOf fuel' false sc ns T with
    | .sort 0 => pure .prop
    | .any => pure .any
    | _ => pure .other
  match T with
  | .sort l => pure (.sort l)
  | .pi hs ds c => do
    let (sc', ns', _) ← telescope fuel' false sc ns hs ds
    pure (.pi (← typeDecl fuel' false sc' ns' c vis))
  | .ref A => pure (.ref (← typeDecl fuel' false sc ns A vis))
  | .val v => valTypeDecl fuel' v
  | .letIn h u w => do
    let d ← declOf fuel' false sc ns u
    typeDecl fuel' false (d :: sc) (h.name :: ns) w vis
  | .seq _ w => typeDecl fuel' false sc ns w vis
  | .matchNat _ z s =>
    pure (agreeTypeDecl [← typeDecl fuel' false sc ns z vis, ← typeDecl fuel' false sc ns s vis])
  | .matchInd _ _ arms =>
    pure (agreeTypeDecl (← arms.mapM fun (_, a) => typeDecl fuel' false sc ns a vis))
  | .call (.const F) _ _ => typeFnDecl fuel' F vis fallback
  | .const F => do
    -- a constant that is a type (`T0 : Type₁ := Π(x : &Nat). Prop`): its closed value's head,
    -- the same on every path; only a Π-type is read through it, as for type functions
    match (← get).globals.find? (·.name == F) with
    | some g => match g.fn?, g.val with
      | none, v@(.tPi ..) => valTypeDecl fuel' v
      | _, _ => fallback
    | none => fallback
  | _ => fallback
termination_by structural fuel

/-- D77: what a call of the global `F` says as a type, when `F` is a type function: its body's
reading as a type (`typeDecl`), in the scope of its declared parameters (and itself). `dflt`
when `F` is not a type function or is being unfolded already. -/
def typeFnDecl (fuel : Nat) (F : String) (vis : List String) (dflt : M DeclInfo) : M DeclInfo := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- inside its own body a recursive type function says nothing new: its reading is the
  -- agreement of its other arms (`.any` agrees with every arm)
  if vis.contains F then return .any
  let some g := (← get).globals.find? (·.name == F) | return ← dflt
  let some (.fix _ hs ds c _ body) := g.fn? | return ← dflt
  unless c matches .sort _ do return ← dflt
  let (sc', ns', _) ← telescope fuel' false [] [] hs ds
  let k := ds.length
  let d ← typeDecl fuel' false (sc'.take k ++ [DeclInfo.pi (.sort 0)]) (ns'.take k ++ [F]) body (F :: vis)
  -- only a Π-type is read through the body: a body that computes to a sort or a proposition
  -- keeps the call's declared reading (D35, D55: `U(n)` computing to `Prop` is not a sort, so a
  -- function into `U(n)` returns data, `ErasureBySyntax.W`; `Fording.Sneak`), and a conflict
  -- between the arms' erasure classes is the call's reading, rejected where it is used
  match d with
  | .pi _ | .conflict => pure d
  | _ => dflt
termination_by structural fuel

/-- A term written where a type is expected: with `chk`, its declared type must be a sort
(D55). Returns the sort (`1` when not known). -/
def typePos (fuel : Nat) (chk : Bool) (sc : List DeclInfo) (ns : List String) (T : Term) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !chk then return 1
  match ← declOf fuel' chk sc ns T with
  | .sort l => pure l
  | .any => pure 1
  | .conflict => err (conflictMsg T ns)
  | _ =>
    err s!"[D55] {T.pp ns} is written where a type is expected, but its declared type is not a sort (it is a type only by computation)"
termination_by structural fuel

/-- A telescope of binder types, each in the scope of the earlier ones: the extended
scope, and the largest of their sorts. -/
def telescope (fuel : Nat) (chk : Bool) (sc : List DeclInfo) (ns : List String) (hs : List Hint)
    (ds : List Term) : M (List DeclInfo × List String × Nat) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let mut sc := sc
  let mut ns := ns
  let mut l := 0
  for (h, d) in hs.zip ds do
    l := max l (← typePos fuel' chk sc ns d)
    sc := (← typeDecl fuel' chk sc ns d) :: sc
    ns := h.name :: ns
  pure (sc, ns, l)
termination_by structural fuel

/-- What a runtime value's declared type says (an embedded value, a capture). -/
def valueDecl (fuel : Nat) (v : Value) : M DeclInfo := withLive false do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match v with
  | .proof => pure .prop
  | .sort l => pure (.sort (sortSucc l))
  | .tNat | .tUnit | .tRef _ | .tInd .. | .tEq .. | .tPi .. =>
    pure (.sort (← sortOf fuel' v))
  | .gfn n => valTypeDecl fuel' (← lookupGlobal n).ty
  | .clo cs (.fix _ hs ds c _ _) => do
    let capSc ← cs.reverse.mapM (valueDecl fuel')
    let (sc', ns', _) ← telescope fuel' false capSc [] hs ds
    pure (.pi (← typeDecl fuel' false sc' ns' c))
  | .abs σ => valTypeDecl fuel' (← absType σ)
  | .sealed t => declOf fuel' false [] [] t
  | .borrow _ _ => pure (.ref .other)
  | _ => pure .other
termination_by structural fuel

/-- What a type value says as a declared type (a stored or global type). -/
def valTypeDecl (fuel : Nat) (T : Value) : M DeclInfo := withLive false do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match T with
  | .sort l => pure (.sort l)
  | .tPi cs (.pi hs ds c) => do
    let capSc ← cs.reverse.mapM (valueDecl fuel')
    let (sc', ns', _) ← telescope fuel' false capSc [] hs ds
    pure (.pi (← typeDecl fuel' false sc' ns' c))
  | .tRef A => pure (.ref (← valTypeDecl fuel' A))
  | _ => pure (if ← isPropV fuel' T then .prop else .other)
termination_by structural fuel

/-- What each parameter's declared type says, each in the scope of the captured values
and the earlier parameters, and what the codomain says. -/
def paramDecls (fuel : Nat) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    M (List DeclInfo × DeclInfo) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let capSc ← cs.reverse.mapM (valueDecl fuel')
  let (sc', ns', _) ← telescope fuel' false capSc [] hs ds
  pure ((sc'.take ds.length).reverse, ← typeDecl fuel' false sc' ns' c)

/-- A binding's declared reading, which every decision about the binding reads (its erasure,
whether a call through it is a statement). It is its declared type's reading as a type
(`typeDecl`): read from syntax and declared types alone, the same on both evaluation paths.

D77 (`notes/stability.md`, site 7): this used to be completed from values, for a declared
type that is a Π-type only after computing (`p : Pow(Nat)`): from the evaluated type, or from
the value bound (a closure's own Π-type, an abstract value's type). A sealed function value
at an instance has neither, so the instance read `other` (data) where the generic call read
the evaluated Π-type's class, and the pre-pass and the run then disagreed (`Inst` in
`Examples/Stability.lean`). `typeDecl` now reads a type function's Π-type off its body, which
makes the completion unnecessary. A type whose arms are Π-types erased differently has no
class, and a binding of it is rejected. -/
def refineDecl (d : DeclInfo) : M DeclInfo := do
  if d == .conflict then
    err "[D77] this binding's type is computed by a type function whose arms are Π-types whose calls are erased differently (some return types or proofs, some data): its erasure class would be decided by computation"
  pure d

/-- Whether a statement argument runs in place rather than on a private copy (`stmtArgIf`):
exactly when its declared type is a borrow type. D77 (`notes/stability.md`, site 6): this used
to be read off the argument's value (does it hold a borrow or a loan), which equals the type
test only on well-formed states (A.5 condition 5, and no borrows in data), an invariant of the
machine that is not proved. Read from the declared type, the two paths agree by construction. -/
def stmtArgInPlace (fuel : Nat) (a : Term) : M Bool := do
  pure ((← withLive true (declOf fuel false [] [] a)) matches .ref _)

/-- Push captured values as bindings, each with what its declared type says. -/
def pushCaps (fuel : Nat) (cs : List Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for v in cs do
    let d ← valueDecl fuel' v
    modifyFrame (← topIdx) fun fr =>
      { fr with binds := fr.binds.push { hint := ⟨"κ"⟩, ty := none, val := v, decl := d, cap := true } }

/-- Is a type a proposition? (P5, and proof irrelevance: a value of a proposition is `⋆`.) -/
def isPropV (fuel : Nat) (T : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match T with
  | .tEq .. => pure true
  | .tInd n _ => pure ((← lookupInd n).sort == 0)
  | .tNat | .tUnit | .tRef _ | .sort _ => pure false
  | .tPi _ _ => pure ((← fnClass fuel' T) == 2)
  | .abs σ => pure ((← absType σ) == .sort 0)
  | .sealed t => pure ((← sealedSort? t) == some 0)
  | _ => pure false
termination_by structural fuel

/-- A value standing for an arbitrary inhabitant of `A`, used only to compute sorts. -/
def genericValue (fuel : Nat) (A : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if ← isPropV fuel' A then return .proof
  match A with
  | .tRef T => pure (.borrow (← freshLoan) (← absOf T))
  | _ => absOf A

/-- The erasure class of a function type (D28, D35): 1 = it returns types, 2 = it
returns proofs, 0 = it returns data. v1.7: read off the codomain *term*, for top-level
and local functions alike: types if it is syntactically a sort, proofs if its declared
sort is `Prop` (`typeDecl`, D63), never by evaluating it (formal-appendix BoomL). The
function of a stuck block (codomain `.val B`, the match's type) returns proofs if `B`
has sort `Prop` and data otherwise, so the block is erased exactly when its match is
(BoomB). Cached per Π-type. -/
def fnClass (fuel : Nat) (piTy : Value) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match (← get).classCache.lookup piTy with
  | some k => return k
  | none => pure ()
  let k ← match piTy with
    | .tPi cs (.pi hs ds c) =>
      match c with
      | .sort _ => pure 1
      | .val _ => pure 0     -- a stuck block's function (`closeBlock`): its class is given at its call
      | _ =>
        -- read from the codomain term, never evaluated (D35), by the one reader of declared
        -- types (`typeDecl`, D63): proofs if the codomain's declared sort is `Prop`
        let capSc ← cs.reverse.mapM (valueDecl fuel')
        let (sc', ns', _) ← telescope fuel' false capSc [] hs ds
        pure (if (← typeDecl fuel' false sc' ns' c).isProof then 2 else 0)
    | _ => pure 0
  modify fun s => { s with classCache := (piTy, k) :: s.classCache }
  pure k
termination_by structural fuel

/-- v1.7 (D35): which parameters are proofs, i.e. declared of sort Prop, read by the one
reader of declared types (`typeDecl` over the telescope, in the scope of the captured values and
the earlier parameters, D63). The same flags wherever parameters are bound: the body, [Def]
and [Call-type]. -/
def paramFlags (fuel : Nat) (cs : List Value) (ds : List Term) : M (List Bool) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let quick : Term → Bool := fun
    | .nat | .unit | .ref _ | .sort _ | .tind "Pair" _ => true
    | _ => false
  if ds.all quick then return ds.map fun _ => false
  let capSc ← cs.reverse.mapM (valueDecl fuel')
  let (sc', _, _) ← telescope fuel' false capSc [] (ds.map fun _ => ⟨"_"⟩) ds
  pure ((sc'.take ds.length).reverse.map (·.isProof))

/-- Is this leaf (a place, constant or `λ`) a proof, i.e. declared of sort Prop? A
variable by its binding's flag (`letIn`, `paramFlags`); a constructor field by its
declared type (v2.0: a parameter declared `: Prop`, or a Prop inductive); other
sub-places and captured values never are. -/
def leafProof (fuel : Nat) (t : Term) (v : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match t with
  | .place (.var i) => match ← varPos i with
    | .bind f j => pure (← get).env[f]!.binds[j]!.proof
    | _ => pure false
  | .place (.field g _) => fieldIsProof g      -- v2.0: a field declared of a proposition
  | .const n => pure (← valTypeDecl fuel' (← lookupGlobal n).ty).isProof
  | .fix .. => match v with
    | .proof => pure true
    | .clo cs (.fix _ hs ds c _ _) => pure ((← fnClass fuel' (.tPi cs (.pi hs ds c))) == 2)
    | _ => pure false
  | _ => pure false

/-- The class of a declared type: a sort (its inhabitants are types), a proposition
(its inhabitants are proofs), or data. Read off the type's constructor or, for a
sealed type, off its head call's declared codomain; never by normalising further. -/
def typeClass (fuel : Nat) (T : Value) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match T with
  | .sort _ => pure 1
  | .tEq .. => pure 2
  | .tInd n _ => pure (if (← lookupInd n).sort == 0 then 2 else 0)
  | .tPi _ _ => pure (if (← fnClass fuel' T) == 2 then 2 else 0)
  | .sealed t => pure (if (← sealedSort? t) == some 0 then 2 else 0)
  | .abs σ => match ← absType σ with
    | .sort 0 => pure 2
    | _ => pure 0
  | _ => pure 0

/-- `J(A, a, b, P, h, t)` is a proof when the motive returns propositions. -/
def jErased (fuel : Nat) (P : Term) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pure ((← withLive true (declOf fuel' false [] [] P)) matches .pi (.sort 0))

def kindOf (fuel : Nat) (B : Value) : M Kind := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if ← isPropV fuel' B then return .prop
  match B with
  | .tUnit => pure .unit
  | .tRef _ => pure .ref
  | _ => pure .data

/-- [Close]'s row read from the declared codomain `B` (v1.7, D35): syntactically `Unit`,
`&T`, or anything else. A stuck block's codomain is the match's type. -/
def declKind (fuel : Nat) (piTy : Value) : M Kind := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match piTy with
  | .tPi _ (.pi _ _ c) => match c with
    | .unit => pure .unit
    | .ref _ => pure .ref
    | .val B => do let k ← kindOf fuel' B; pure (if k == .prop then .data else k)
    | _ => pure .data
  | _ => err s!"not a function type: {piTy}"

end

end Ochr
