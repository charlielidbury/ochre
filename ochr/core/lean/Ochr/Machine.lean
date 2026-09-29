import Ochr.Obs

/-!
# The machine (RULES §3), observation and `Id` (§4), and typing (§5)

One evaluator serves the machine and the checker (RULES §5: "typing is the machine
on symbolic inputs, plus case splitting"). `eval typed t`:
* `typed = false` is the plain machine of §3. It runs callee bodies and [Seal] runs;
  a match on a neutral is stuck, and the innermost enclosing call closes off ([Close]).
* `typed = true` runs the checked program and the terms inside the types it forms. It
  also computes types, checks arguments ([Call-type]), checks [Rec], and a match on an
  abstract `σ` is split ([Split]): in tail position each arm is checked to the end
  (`checkTail`); otherwise the arms are checked and the match is closed off as a stuck
  block (`closeOffMatch`), and evaluation continues once from there.

Everything that runs the machine is in one `mutual` block, because normalising a
sealed program ([Seal]) runs the machine, substitution ([End], refinement)
normalises, and forming a type (`Id`) runs observations.
-/

namespace Ochr

/-- Print a place with the names of the top frame's bindings. -/
def ppPlace (p : Place) : M String := do
  let f ← topIdx
  let names := (← get).env[f]!.binds.toList.reverse.map (·.hint.name)
  pure (p.pp names)

/-- The content of a place (RULES §3: follow `x`, `*p` through `borrow_ℓ v` to `v`,
`p.1` through `S v` to `v`). -/
def content (p : Place) : M Value := do
  let (i, ss) := p.steps
  let v ← getAt (← varPos i)
  match v.follow ss with
  | some w => pure w
  | none => err s!"no such place {← ppPlace p}: its path does not exist in {v}"

def setPlace (p : Place) (new : Value) : M Unit := do
  let (i, ss) := p.steps
  let pos ← varPos i
  let v ← getAt pos
  match v.updAt (fun _ => new) ss with
  | some v' => setAt pos v'
  | none => err s!"no such place {← ppPlace p}: its path does not exist in {v}"

/-- The first live loan met on the path to a place, including at the place itself. -/
def firstLiveLoanOnPath (env : Env) : Value → List Step → Option Nat
  | .loan l, _ => if liveLoan env l then some l else none
  | v, s :: ss => (stepV s v).bind (firstLiveLoanOnPath env · ss)
  | _, [] => none

def firstBorrowLabel : Value → Option Nat
  | .borrow l _ => some l
  | .succ w => firstBorrowLabel w
  | _ => none

/-- What a call's result type is, for [Close]'s table and for P5. -/
inductive Kind where
  | prop | unit | ref | data
deriving BEq, Inhabited

/-- A syntactic guess at whether a type term denotes a proposition. -/
partial def isPropTerm? : Term → Option Bool
  | .id .. | .eq .. => some true
  | .nat | .unit | .ref _ | .tind "Pair" _ | .sort _ => some false
  | .pi _ _ c => isPropTerm? c
  | _ => none

def syntacticKind? : Term → Option Kind
  | .unit => some .unit
  | .ref _ => some .ref
  | t => (isPropTerm? t).map fun b => if b then .prop else .data

/-- Is this term literally the sort `Prop`? -/
def isPropSort : Term → Bool
  | .sort 0 | .val (.sort 0) => true
  | _ => false

/-- v1.7 (D35): what a parameter's declared type says about the parameter, for reading
erasure classes off syntax: 1 = it is a proposition (declared `: Prop`), 2 = it is a
function into propositions (declared `: Π(…). Prop`), 0 = neither (or not known). -/
def declOfDom : Term → Nat
  | .sort 0 | .val (.sort 0) => 1
  | .pi _ _ c => if isPropSort c then 2 else 0
  | _ => 0

/-- Does `self` (tested by `isSelf depth term`) occur in `t` only as the head of a
call? (Fix L1 of this checker; see notes/lean-checker.md.) -/
partial def headOnly (isSelf : Nat → Place → Bool) (c : Nat) : Term → Bool
  | .call (.place p) as _ =>
      ((isSelf c p && (p matches .var _)) || !isSelf c p) && as.all (headOnly isSelf c)
  | .place p | .borrow p => !isSelf c p
  | .assign p t => !isSelf c p && headOnly isSelf c t
  | .letIn _ t u => headOnly isSelf c t && headOnly isSelf (c + 1) u
  | .matchNat p z s => !isSelf c p && headOnly isSelf c z && headOnly isSelf c s
  | .pi _ ds cod => (ds.zipIdx.all fun (d, i) => headOnly isSelf (c + i) d)
      && headOnly isSelf (c + ds.length) cod
  | .fix _ _ ds cod _ b => (ds.zipIdx.all fun (d, i) => headOnly isSelf (c + i) d)
      && headOnly isSelf (c + ds.length) cod && headOnly isSelf (c + ds.length + 1) b
  | .call f as _ => headOnly isSelf c f && as.all (headOnly isSelf c)
  | .seq t u | .cong t u | .ascribe t u =>
      headOnly isSelf c t && headOnly isSelf c u
  | .succ t | .fst t | .snd t | .ref t => headOnly isSelf c t
  | .eq a b d | .id a b d => headOnly isSelf c a && headOnly isSelf c b && headOnly isSelf c d
  | .ctor _ _ _ ps as => (ps ++ as).all (headOnly isSelf c)
  | .prim _ as | .tind _ as => as.all (headOnly isSelf c)
  | .matchInd p _ as => !isSelf c p && as.all (headOnly isSelf c ·.2)
  | _ => true

/-- Same check for a top-level definition, whose self-reference is `const name`. -/
partial def constHeadOnly (n : String) : Term → Bool
  | .call (.const _) as _ => as.all (constHeadOnly n)
  | .const m => m != n
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => constHeadOnly n t
  | .letIn _ t u | .seq t u | .cong t u
  | .ascribe t u => constHeadOnly n t && constHeadOnly n u
  | .matchNat _ z s => constHeadOnly n z && constHeadOnly n s
  | .pi _ ds c => ds.all (constHeadOnly n) && constHeadOnly n c
  | .fix _ _ ds c _ b => ds.all (constHeadOnly n) && constHeadOnly n c && constHeadOnly n b
  | .call f as _ => constHeadOnly n f && as.all (constHeadOnly n)
  | .eq a b d | .id a b d => constHeadOnly n a && constHeadOnly n b && constHeadOnly n d
  | .ctor _ _ _ ps as => (ps ++ as).all (constHeadOnly n)
  | .prim _ as | .tind _ as => as.all (constHeadOnly n)
  | .matchInd _ _ as => as.all (constHeadOnly n ·.2)
  | _ => true

/-- The refined entry value of `σ`: `σ` with the [Split] refinements made so far
substituted, recursively. -/
partial def expandRefs (refs : List (Nat × Value)) : Value → Value
  | .abs σ => match refs.lookup σ with
      | some r => expandRefs refs r
      | none => .abs σ
  | .succ v => .succ (expandRefs refs v)
  | .ind t c h ps fs => .ind t c h ps (fs.map (expandRefs refs))
  | v => v

/-- v2.0 (D46): infer an inductive's parameters by matching a field's declared type
term `FT` (in the scope of the `np` parameters) against the type `T` of the value given
for it. Only unsolved parameters are filled; the field types are checked afterwards. -/
partial def unifyParams (np : Nat) (FT : Term) (T : Value) (sol : Array (Option Value)) :
    Array (Option Value) :=
  match FT, T with
  | .place (.var j), _ =>
    if j < np && (sol[np - 1 - j]!).isNone then sol.set! (np - 1 - j) (some T) else sol
  | .tind m as, .tInd m' vs =>
    if m == m' && as.length == vs.length then
      (as.zip vs).foldl (fun s (a, v) => unifyParams np a v s) sol
    else sol
  | _, _ => sol

/-- The strict subterms of a value built from `S`. -/
partial def strictSubterms : Value → List Value
  | .succ v => v :: strictSubterms v
  | .ind _ _ _ _ fs => fs.flatMap fun f => f :: strictSubterms f
  | _ => []

mutual

-- ### Substitution and normal forms ([Seal], refinement, [End])

/-- Substitute `r` for the variable `x` (an abstract value `σ` or a loan) in a value.
Values are kept in normal form (RULES §3 [Seal]): a sealed program that changed is
re-normalised (inner ones first, since the traversal rebuilds bottom-up), and `Eq`
and `∧` are rebuilt with their smart constructors. -/
partial def substV (x r : Value) (v : Value) : M Value := do
  if !(v.anyAtom (· == x)) then return v
  if v == x then return r
  match v with
  | .abs _ | .loan _ => return (if v == x then r else v)
  | .succ w => return .succ (← substV x r w)
  | .borrow l w => return .borrow l (← substV x r w)
  | .clo cs t => return .clo (← cs.mapM (substV x r)) (← substT x r t)
  | .tPi cs t => return .tPi (← cs.mapM (substV x r)) (← substT x r t)
  | .sealed t => nfSealed (← substT x r t)
  | .tEq A a b => mkEqM (← substV x r A) (← substV x r a) (← substV x r b)
  | .tInd n as => return mkTInd n (← as.mapM (substV x r)) (← get).cfg.unitNorm
  | .tRef A => return .tRef (← substV x r A)
  | .ind t c h ps fs => return .ind t c h (← ps.mapM (substV x r)) (← fs.mapM (substV x r))
  | _ => return v

partial def substT (x r : Value) (t : Term) : M Term := do
  if !(t.anyAtom (· == x)) then return t
  let go := substT x r
  match t with
  | .val v => return .val (← substV x r v)
  | .assign p u => return .assign p (← go u)
  | .letIn h u w => return .letIn h (← go u) (← go w)
  | .seq u w => return .seq (← go u) (← go w)
  | .matchNat p z s => return .matchNat p (← go z) (← go s)
  | .pi hs ds c => return .pi hs (← ds.mapM go) (← go c)
  | .fix h hs ds c d b => return .fix h hs (← ds.mapM go) (← go c) d (← go b)
  | .call f as hd => return .call (← go f) (← as.mapM go) hd
  | .succ u => return .succ (← go u)
  | .fst u => return .fst (← go u)
  | .snd u => return .snd (← go u)
  | .ref u => return .ref (← go u)
  | .cong a b => return .cong (← go a) (← go b)
  | .ascribe a b => return .ascribe (← go a) (← go b)
  | .eq a b c => return .eq (← go a) (← go b) (← go c)
  | .id a b c => return .id (← go a) (← go b) (← go c)
  | .prim n as => return .prim n (← as.mapM go)
  | .ctor ty c h ps as => return .ctor ty c h (← ps.mapM go) (← as.mapM go)
  | .tind n as => return .tind n (← as.mapM go)
  | .matchInd p ty as => return .matchInd p ty (← as.mapM fun (h, a) => do pure (h, ← go a))
  | _ => return t

/-- Substitute in every value of Ω; with `types`, also in the stored types, the types
of abstract values and the goal ([Split]: "applied to Ω, the goal and all stored
types"). -/
partial def substEnv (x r : Value) (types : Bool) : M Unit := do
  for p in allPos (← get).env do
    setAt p (← substV x r (← getAt p))
    if types then
      if let .bind f i := p then
        if let some T := (← get).env[f]!.binds[i]!.ty then
          let T' ← substV x r T
          modifyFrame f fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }
  if types then
    let tys := (← get).absTy
    let mut tys' := #[]
    for T in tys do tys' := tys'.push (← substV x r T)
    modify fun s => { s with absTy := tys' }
    if let some g := (← get).goal then
      let g' ← substV x r g
      modify fun s => { s with goal := some g' }

/-- [Seal] `nf(⌈t⌉)`: run `t` from the empty environment. Its head call is marked
(`Term.call _ _ true`) and is not eligible for [Close]; loans whose borrow is outside
the run are inert (they have no borrow in the run's Ω). If the run completes, the
result is its value; if it is stuck, `⌈t⌉` (its embedded values are already normal). -/
partial def nfSealed (t : Term) : M Value := do
  let saved ← get
  -- bounded like calls, so that a normalisation loop (breaker-fresh-v16 X5 without D39)
  -- is an error rather than a stack overflow
  if saved.depth ≥ 2000 then err "normalisation depth exceeded (a sealed program that re-closes itself)"
  modify fun s => { s with env := #[{}], depth := s.depth + 1 }
  let r ← tryCatch (do let (v, _) ← eval false t; pure (some v)) fun e =>
    match e with
    | .stuck f => do modify (fun s => { s with fuel := f }); pure none
    | .error m => throw (.error m)
  restoreKeep saved
  match r with
  | some v => pure v
  | none => canonNeutral (.sealed t)

-- ### Borrows: [End], [Access], [Read], [Borrow], [Assign], [Drop]

/-- [End ℓ]: replace `borrow_ℓ v` by `⊥` and substitute `v` for every `loan_ℓ`. A loan
whose borrow is not in Ω is inert: nothing happens. -/
partial def endBorrow (l : Nat) : M Unit := do
  let env := (← get).env
  match findBorrow env l with
  | none => pure ()
  | some p =>
    match (valAt env p).takeBorrow l with
    | none => pure ()
    | some (c, rest) =>
      setAt p rest
      substEnv (.loan l) c false

/-- End every borrow in Ω (for observations, §4). -/
partial def endAll : M Unit := do
  let env := (← get).env
  match (allPos env).findSome? (fun p => firstBorrowLabel (valAt env p)) with
  | some l => endBorrow l; endAll
  | none => pure ()

/-- [Access], path part: end every borrow whose loan is on the path to `p`. -/
partial def accessPath (p : Place) : M Unit := do
  let (i, ss) := p.steps
  let env := (← get).env
  match firstLiveLoanOnPath env (valAt env (← varPos i)) ss with
  | some l => endBorrow l; accessPath p
  | none => pure ()

/-- [Access], content part: end every borrow whose loan occurs inside `content(p)`. -/
partial def accessInside (p : Place) : M Unit := do
  if !(← get).cfg.accessInside then return
  let v ← content p
  match liveLoansIn (← get).env v with
  | l :: _ => endBorrow l; accessInside p
  | [] => pure ()

/-- [Access] for matching (v1.5, D29): a loan anywhere inside a neutral at the head of
`content(p)` counts as being at the head (its position inside the neutral is unknown),
so its borrow ends. -/
partial def accessNeutralHead (p : Place) : M Unit := do
  if !(← get).cfg.matchEndsInside then return
  let v ← content p
  match v with
  | .sealed _ | .abs _ =>
    match liveLoansIn (← get).env v with
    | l :: _ => endBorrow l; accessNeutralHead p
    | [] => pure ()
  | _ => pure ()

/-- [Read]: borrow-free content is copied; a borrow is moved out (`p ↦ ⊥`). -/
partial def readPlace (p : Place) : M Value := do
  accessPath p; accessInside p
  let v ← content p
  match v with
  | .bot => err s!"[Read] {← ppPlace p} was moved out or its borrow ended (reading ⊥)"
  | .borrow _ _ => logEffect p "moves"; setPlace p .bot; pure v
  | _ => pure v

/-- D41: record an assignment, borrow or move of `p` by its root position. -/
partial def logEffect (p : Place) (kind : String) : M Unit := do
  if (← get).cfg.confine then
    if let .bind f i ← varPos p.root then
      let root := (← get).env[f]!.binds[i]!.hint.name
      modify fun s => { s with effects := s.effects.push { f, i, kind, place := p, root } }

/-- D41: the run since the log had `start` entries is confined with respect to the
state it started from (frames below `f0`, and the first `n0` bindings of frame `f0`):
none of its steps assigned, borrowed or moved a place rooted there. -/
partial def checkConfined (start f0 n0 : Nat) (what : String) : M Unit := do
  if let some m ← confinementViolation start f0 n0 what then err m

partial def confinementViolation (start f0 n0 : Nat) (what : String) : M (Option String) := do
  let es := (← get).effects
  for e in es.extract start es.size do
    if e.pending || e.f < f0 || (e.f == f0 && e.i < n0) then
      return some s!"[D41] {what} {e.desc}, a place that outlives it (an erased term may affect outer places only by passing them to an erased call)"
  pure none

/-- D41, at the end of an erased run: a step on a place created inside the run is local
to it (resolved, dropped); a step on a place of the start state stays, marked pending. -/
partial def settleErased (start f0 n0 : Nat) : M Unit := do
  if (← get).effects.size == start then return
  modify fun s =>
    let (keep, rest) := (s.effects.extract 0 start, s.effects.extract start s.effects.size)
    let outer := rest.filterMap fun e =>
      if e.f < f0 || (e.f == f0 && e.i < n0) then some { e with pending := true } else none
    { s with effects := keep ++ outer }

/-- D41: a type position is erased; run it on a private copy, confined. -/
partial def confinedCopy {α : Type} (what : String) (x : M α) : M α := onCopy do
  let st ← get
  let start := st.effects.size
  let f0 := st.env.size - 1
  let n0 := st.env[f0]!.binds.size
  let r ← x
  if (← get).cfg.confine then checkConfined start f0 n0 s!"{what}, an erased term,"
  pure r

/-- D41, in a context that is not erased: an erased run below it that affected a place
outliving it is a type error. -/
partial def flushPending (start : Nat) : M Unit := do
  let es := (← get).effects
  if es.size == start then return
  for e in es.extract start es.size do
    if e.pending then
      err s!"[D41] an erased term {e.desc}, a place that outlives it (an erased term may affect outer places only by passing them to an erased call)"

/-- [Borrow] `&p ⇓ borrow_ℓ v` with `p ↦ loan_ℓ`. -/
partial def borrowPlace (p : Place) : M Value := do
  accessPath p; accessInside p
  let v ← content p
  match v with
  | .bot => err s!"[Borrow] {← ppPlace p} was moved out (borrowing ⊥)"
  | .borrow _ _ => err "[Borrow] a borrow of a borrow (&&T is outside the core)"
  | _ =>
    logEffect p "borrows"
    let l ← freshLoan
    setPlace p (.loan l)
    pure (.borrow l v)

/-- [Assign] with the value already computed: drop the old content, store the new. -/
partial def assignPlace (p : Place) (v : Value) : M Unit := do
  pushTemp v
  accessPath p; accessInside p
  let old ← content p
  match old with
  | .borrow l _ => endBorrow l
  | _ =>
    if !(liveLoansIn (← get).env old).isEmpty then
      err s!"[Drop] the old content of {← ppPlace p} is overwritten while borrowed"
  let v' ← popTemp
  logEffect p "assigns"
  setPlace p v'

/-- [Drop] the most recent binding of the top frame: a borrow ends; an owned value
holding a live loan is an error (something borrows a dying place). -/
partial def dropTopBind : M Unit := do
  let f ← topIdx
  let some b := (← get).env[f]!.binds.back? | err "internal: no binding to drop"
  match b.val with
  | .borrow l _ => endBorrow l
  | v =>
    if !(liveLoansIn (← get).env v).isEmpty then
      err s!"[Drop] {b.hint.name} goes out of scope while it is borrowed"
  modifyFrame f fun fr => { fr with binds := fr.binds.pop }

/-- [Drop] a discarded value (`t; u`). -/
partial def dropValue (v : Value) : M Unit := do
  pushTemp v
  match v with
  | .borrow l _ => endBorrow l
  | _ =>
    if !(liveLoansIn (← get).env v).isEmpty then
      err "[Drop] a discarded value holds a live loan"
  discard popTemp

/-- Pop the top frame, dropping its bindings (most recent first). -/
partial def popFrame : M Unit := do
  let f ← topIdx
  let n := (← get).env[f]!.binds.size
  for _ in [0:n] do dropTopBind
  discard popFrameRaw

-- ### Types

/-- The type of a place, read off the stored types (RULES §5; e1 F9). -/
partial def placeType (p : Place) : M Value := do
  match p with
  | .var i =>
    let pos ← varPos i
    match ← tyAt pos with
    | some T => pure T
    | none => valType (← getAt pos)
  | .deref q => match ← placeType q with
    | .tRef T => pure T
    | T => err s!"*{← ppPlace q}: not a borrow (type {T})"
  | .fst q => match ← placeType q with
    | .tNat => pure .tNat
    | .tInd "Pair" [A, _] => pure A           -- field 1 of the library's Pair (D52)
    | T => err s!"{← ppPlace q}.1: no sub-place at type {T}"
  | .snd q => match ← placeType q with
    | .tInd "Pair" [_, B] => pure B
    | T => err s!"{← ppPlace q}.2: no sub-place at type {T}"
  | .field g q => match ← placeType q with
    | .tInd n ps =>
      -- the place names its constructor (v2.0), so a proof's field has a type too
      if n != g.ty then err s!"{← ppPlace q}.{g.name}: a field of {g.ty}, at type {n}"
      match (← fieldTypes (← lookupInd n) ps g.ctor)[g.idx]? with
      | some (_, T) => pure T
      | none => err s!"{← ppPlace q}.{g.name}: no such field"
    | T => err s!"{← ppPlace q}.{g.name}: no field at type {T}"

/-- The type of a value, for untyped bindings (captured values) and embedded values. -/
partial def valType (v : Value) : M Value := do
  match v with
  | .zero | .succ _ => pure .tNat
  | .unit => pure .tUnit
  | .abs σ => absType σ
  | .gfn n => pure (← lookupGlobal n).ty
  | .clo cs (.fix _ hs ds c _ _) => pure (.tPi cs (.pi hs ds c))
  | .borrow _ w => pure (.tRef (← valType w))
  | .ind t c _ ps fs => if ps.isEmpty then indValType t c fs else pure (.tInd t ps)   -- D49 (4)
  | .tNat | .tUnit | .tEq .. | .tRef _ | .tPi .. | .sort _ | .tInd .. =>
    pure (.sort (← sortOf v))
  | .sealed t =>
    if (← get).cfg.capTypes then sealedType t
    else err s!"cannot infer the type of the value {v}"
  | _ => err s!"cannot infer the type of the value {v}"

/-- The type of a sealed program (neutral data, e.g. a captured one): its term typed as
an ordinary term on a private copy, from the empty environment. Its head call is not
marked, so a stuck body closes off; its [Call-type] is what gives the type. -/
partial def sealedType (t : Term) : M Value := onCopy do
  modify fun s => { s with env := #[{}], recStack := [], recCands := [], goal := none }
  let (_, T) ← eval true t.unHead
  match T with
  | some T => pure T
  | none => err s!"cannot infer the type of the sealed program ⌈{t.pp []}⌉"

-- ### Inductive declarations (v2.0: D45–D47)

/-- The field types of constructor `c` of `d` at the parameters `ps` (D46): the declared
field type terms, evaluated in a frame binding the parameters. -/
partial def fieldTypes (d : IndDecl) (ps : List Value) (c : Nat) : M (List (String × Value)) := do
  let some (_, fields) := d.ctors[c]? | err s!"{d.name} has no constructor {c}"
  if ps.length != d.params.length then
    err s!"{d.name} takes {d.params.length} parameters, given {ps.length}"
  onCopy do
    pushFrame
    for ((h, _), v) in d.params.zip ps do pushBind h none v
    fields.mapM fun (f, FT) => do pure (f, ← evalType FT)

/-- One declared field type at partially known parameters (for a hint; unknown
parameters are bound to `⊥`, which a field type not mentioning them never reads). -/
partial def fieldTypeAt (d : IndDecl) (sol : Array (Option Value)) (FT : Term) : M (Option Value) := do
  let np := d.params.length
  unless FT.freeVars.all fun j => j < np && (sol[np - 1 - j]!).isSome do return none
  tryCatch (onCopy do
      pushFrame
      for ((h, _), v) in d.params.zip sol.toList do pushBind h none (v.getD .bot)
      some <$> evalType FT)
    fun _ => pure none

/-- The type of a constructor value (for untyped bindings): its parameters are inferred
from its fields' types; a parameter no field determines (the `A` of `Nil`) is unknown. -/
partial def indValType (t : String) (c : Nat) (fs : List Value) : M Value := do
  let d ← lookupInd t
  if d.params.isEmpty then return .tInd t []
  let some (cn, fields) := d.ctors[c]? | err s!"{t} has no constructor {c}"
  let mut sol := Array.replicate d.params.length none
  for (v, (_, FT)) in fs.zip fields do
    sol := unifyParams d.params.length FT (← valType v) sol
  match sol.toList.mapM id with
  | some ps => pure (mkTInd t ps (← get).cfg.unitNorm)
  | none => err s!"cannot infer the parameters of the value {cn}(…) of {t}"

/-- D42 (v2.0): a constructor application of a Prop inductive is a proof, erased. -/
partial def ctorIsProof (ty : String) : M Bool := do
  pure ((← get).cfg.propValues && (← lookupInd ty).sort == 0)

/-- Is a declared field type a proposition, read off the declaration: a parameter
declared `: Prop`, or a Prop inductive. -/
partial def fieldTermIsProp (d : IndDecl) (FT : Term) : M Bool := do
  match FT with
  | .place (.var j) => pure (j < d.params.length && isPropSort (d.params[d.params.length - 1 - j]!).2)
  | .tind m _ => pure ((← lookupInd m).sort == 0)
  | _ => pure false

/-- A field place is a proof iff its declared type is a proposition (syntactic, D42). -/
partial def fieldIsProof (g : FieldRef) : M Bool := do
  let d ← lookupInd g.ty
  match d.ctors[g.ctor]? with
  | some (_, fields) => match fields[g.idx]? with
    | some (_, FT) => fieldTermIsProp d FT
    | none => pure false
  | none => pure false

/-- D45: large elimination (a match on a proof producing a non-proof) is allowed only
from a subsingleton: zero constructors, or one whose fields are all propositions. -/
partial def largeElim (d : IndDecl) : M Bool := do
  match d.ctors with
  | [] => pure true
  | [(_, fields)] => fields.allM fun (_, FT) => fieldTermIsProp d FT
  | _ => pure false

/-- D49 (3): in an arm of a match on a proof, a data field is bound to a fresh abstract
value (as [Def] binds a parameter) and a proof field stays a place holding `⋆`. The arm
becomes `let g = σ; …; arm'`, with the field's place (and places under it) replaced by
the local and every other free place shifted past the new bindings. -/
partial def bindDataFields (p : Place) (d : IndDecl) (ps : List Value) (c : Nat) (arm : Term) : M Term := do
  let some (_, fields) := d.ctors[c]? | return arm
  if !(← get).cfg.proofDataFields then return arm      -- counterfactual: every field is ⋆
  let fts ← fieldTypes d ps c
  let mut datas : Array (Nat × String × Value) := #[]
  for (((fname, FT), (_, T)), i) in (fields.zip fts).zipIdx do
    unless ← fieldTermIsProp d FT do datas := datas.push (i, fname, T)
  if datas.isEmpty then return arm
  let k := datas.size
  let fieldPlace (i : Nat) : Place := .field ⟨d.name, c, i, ""⟩ p
  let body := arm.mapFreePlace (fun dep q =>
    match datas.toList.zipIdx.find? fun ((i, _, _), _) => placePrefix (fieldPlace i) q with
    | some ((i, _, _), j) =>
      let (_, qs) := q.steps
      let (_, fs) := (fieldPlace i).steps
      (qs.drop fs.length).foldl (fun acc st => match st with
        | .deref => .deref acc | .fst => .fst acc | .snd => .snd acc
        | .field g => .field g acc) (Place.var (dep + k - 1 - j))
    | none => q.mapRoot fun r => .var (r + dep + k)) 0
  let mut t := body
  for (_, fname, T) in datas.toList.reverse do
    t := .letIn ⟨fname⟩ (.val (← genericValue T)) t
  pure t

/-- The error of a large elimination from a proof of a non-subsingleton (D45). -/
partial def subsingletonMsg (d : IndDecl) : String :=
  let why := if d.ctors.length ≥ 2 then s!"it has {d.ctors.length} constructors"
    else "its constructor has a field that is not a proposition"
  s!"[D45] a match on a proof of {d.name} returns a non-proof, but {d.name} is not a subsingleton ({why}): large elimination would tell apart proofs that proof irrelevance identifies"

/-- D48 (1): a data type, the only kind of type that may be borrowed: `Nat`, `Unit`, or
an inductive type in `Type₀` (at any parameters, which are themselves in `Type₀`, D46;
pairs are the library's `Pair`, D52). Read off the type's head: a neutral type is not
known to be data. -/
partial def isDataType (T : Value) : M Bool := do
  match T with
  | .tNat | .tUnit => pure true
  | .tInd n _ => pure ((← lookupInd n).sort == 1)
  | _ => pure false

/-- D45: the match `match p { … }` on constructors of `ty` (or with no arms) is by type. -/
partial def byTypeMatch (ty : String) (arms : List (Hint × Term)) : M Bool := do
  if arms.isEmpty then return true
  pure ((← get).cfg.byType && (← lookupInd ty).sort == 0)

/-- The universe level of a type value: `0` is `Prop`. -/
partial def sortOf (T : Value) : M Nat := do
  match T with
  | .tNat | .tUnit | .tRef _ => pure 1
  | .tInd n _ => pure (← lookupInd n).sort
  | .tEq .. => pure 0
  | .sort l => pure (l + 1)
  | .abs σ => match ← absType σ with
    | .sort l => pure l
    | S => err s!"σ{σ} : {S} is not a type"
  | .sealed t => match ← sealedSort? t with
    | some l => pure l
    | none => err s!"{T} is not known to be a type"
  | .tPi cs (.pi hs ds c) => onCopy do
    pushFrame
    for v in cs do pushBind ⟨"κ"⟩ none v
    let mut l := 0
    for (d, h) in ds.zip hs do
      let A ← evalType d
      l := max l (← sortOf A)
      pushBind h (some A) (← genericValue A)
    let lb ← sortOf (← evalType c)
    pure (if lb == 0 then 0 else max l lb)
  | _ => err s!"{T} is not a type"

/-- Is a type a proposition? (P5, and proof irrelevance: a value of a proposition is `⋆`.) -/
partial def isPropV (T : Value) : M Bool := do
  match T with
  | .tEq .. => pure true
  | .tInd n _ => pure ((← lookupInd n).sort == 0)
  | .tNat | .tUnit | .tRef _ | .sort _ => pure false
  | .tPi _ _ => pure ((← fnClass T) == 2)
  | .abs σ => pure ((← absType σ) == .sort 0)
  | .sealed t => pure ((← sealedSort? t) == some 0)
  | _ => pure false

/-- The sort of a sealed program that is a type (v1.4: "a sealed program of sort Prop is
a type"), read off its head call: in result form `L; C`, when the callee's codomain is a
sort. -/
partial def sealedSort? (t : Term) : M (Option Nat) := do
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

/-- A value standing for an arbitrary inhabitant of `A`, used only to compute sorts. -/
partial def genericValue (A : Value) : M Value := do
  if (← get).cfg.p5 && (← isPropV A) then return .proof
  match A with
  | .tRef T => pure (.borrow (← freshLoan) (.abs (← freshAbs T)))
  | _ => pure (.abs (← freshAbs A))

/-- Evaluate a type (P2: once, against the current Ω, on a private copy). -/
partial def evalType (t : Term) : M Value := confinedCopy "a type" do
  let (v, T) ← eval true t
  match T with
  | some (.sort _) => pure v
  | some T => err s!"{t.pp []} is not a type (it has type {T})"
  | none => pure v

/-- Close a `pi`/`fix` term over the current values of its free variables (P2: a
Π-type is a closure over formation-time values, like a λ). Captured values are copied;
closures capture no borrows (RULES §1). -/
partial def capture (t : Term) : M (List Value × Term) := do
  let fvs := (t.freeVars.toArray.qsort (· > ·)).toList   -- oldest binding first
  let m := fvs.length
  let mut vals := #[]
  for o in fvs do
    let p := Place.var o
    accessPath p; accessInside p
    let v ← content p
    match v with
    | .borrow _ _ =>
      let n := ((← get).env.back!.binds[(← get).env.back!.binds.size - 1 - o]!).hint.name
      err s!"a closure or Π-type captures the borrow {n} (closures capture no borrows, RULES §1)"
    | .bot => err "a closure or Π-type captures a moved place"
    | _ => vals := vals.push v
  let idx (o : Nat) : Nat := (fvs.findIdx? (· == o)).getD 0
  let mut t' := t.mapFree (fun c o => .var (c + m - 1 - idx o)) 0
  -- a captured proof keeps its type: its reads are inlined as `(⋆ : T)` (a proof's value
  -- is ⋆, so the type is all there is to record). "A proof" is the binding's declared
  -- flag, never its value (finding P3: `g(0)` may be ⋆ at an instance only)
  if (← get).cfg.capTypes then
    let top := (← get).env.back!
    for (o, k) in fvs.zipIdx do
      let b := top.binds[top.binds.size - 1 - o]!
      if b.proof then
        if let some T := b.ty then
          t' := t'.inlineReads (m - 1 - k) (.ascribe (.val .proof) (.val T)) 0
  pure (vals.toList, t')

/-- D44 (v1.9): a function type returning a borrow must take a borrow (no `'static`
borrows: a returned borrow derives from a borrow argument). -/
partial def borrowParamCheck (ds : List Term) (c : Term) : M Unit := do
  if (← get).cfg.borrowParam && (c matches .ref _) && !(ds.any (· matches .ref _)) then
    err s!"[D44] a function type returning a borrow ({c.pp []}) must have a borrow parameter"

-- ### Conversion (P1, v1.5 D30)

/-- Conversion: same normal form, where the normal form of a function value is the
observation of its generic call (its result and the final contents of the generic
owned places) plus its captured values (D30). Structural everywhere else. -/
partial def conv (v w : Value) : M Bool := do
  if v == w then return true
  -- D50: the unit laws And(True, P) ≡ P ≡ And(P, True) are conversion rules
  let v := unitTop v
  let w := unitTop w
  if v == w then return true
  match v, w with
  | .succ a, .succ b | .tRef a, .tRef b => conv a b
  | .tInd n as, .tInd m bs => pure (n == m && (← convList as bs))
  | .tEq A a b, .tEq B c d => pure ((← conv A B) && (← conv a c) && (← conv b d))
  | .borrow l a, .borrow m b => pure (l == m && (← conv a b))
  | .ind t c _ _ fs, .ind u d _ _ gs => pure (t == u && c == d && (← convList fs gs))
  | .sealed t, .sealed u => convT t u
  | .tPi cs t, .tPi ds u =>
    if (← convList cs ds) && (← convT t u) then return true   -- same captures and code
    if (← get).cfg.piUnder then convPi v w else pure false
  | f, g =>
    let isFn : Value → Bool := fun | .gfn _ | .clo _ _ => true | _ => false
    if isFn f && isFn g then convFn f g else pure false

partial def convList : List Value → List Value → M Bool
  | [], [] => pure true
  | a :: as, b :: bs => do pure ((← conv a b) && (← convList as bs))
  | _, _ => pure false

partial def convTList : List Term → List Term → M Bool
  | [], [] => pure true
  | a :: as, b :: bs => do pure ((← convT a b) && (← convTList as bs))
  | _, _ => pure false

/-- D48 (3): two Π-types are convertible when, their binders instantiated with the same
fresh generic values (a fresh owned place behind each borrow parameter, `⋆` for a proof,
as at [Def]), their domains and their codomains have the same normal forms. Captures
and code are not compared: `Π(n : Nat). Nat where κ1 = σ0` is `Π(n : Nat). Nat`, and a
lemma's statement is compared by what it computes to, as D30 compares functions. A
comparison that errors, gets stuck, or needs itself answers "not convertible". -/
partial def convPi (P Q : Value) : M Bool := do
  let .tPi cs (.pi hs ds c) := P | return false
  let .tPi cs' (.pi _ ds' c') := Q | return false
  if ds.length != ds'.length then return false
  if (← get).convStack.contains (P, Q) then return false
  tryCatch (onCopy do
      modify fun s => { s with env := #[{}], convStack := (P, Q) :: s.convStack }
      pushFrame
      for v in cs do pushBind ⟨"κ"⟩ none v
      let mut ws : Array (Value × Value) := #[]
      for (d, h) in ds.zip hs do
        let A ← evalType d
        let w ← match A with
          | .tRef T =>
            let σ ← freshAbs T
            let l ← freshLoan
            modifyFrame 0 fun fr => { fr with binds := fr.binds.push ⟨⟨s!"{h.name}°"⟩, some T, .loan l, false⟩ }
            pure (Value.borrow l (.abs σ))
          | _ => genericValue A
        pushBind h (some A) w
        ws := ws.push (w, A)
      let C ← evalType c
      discard popFrameRaw
      pushFrame
      for v in cs' do pushBind ⟨"κ"⟩ none v
      for ((d', h), (w, A)) in (ds'.zip hs).zip ws.toList do
        let A' ← evalType d'
        unless ← conv A A' do return false
        pushBind h (some A') w
      let C' ← evalType c'
      conv C C')
    fun _ => pure false

/-- Structural comparison of terms (inside sealed programs, closures and Π-types),
comparing embedded values by `conv`. -/
partial def convT (t u : Term) : M Bool := do
  if t == u then return true
  match t, u with
  | .val v, .val w => conv v w
  | .letIn _ a b, .letIn _ c d | .seq a b, .seq c d
  | .cong a b, .cong c d | .ascribe a b, .ascribe c d =>
    pure ((← convT a c) && (← convT b d))
  | .assign p a, .assign q b => pure (p == q && (← convT a b))
  | .matchNat p z s, .matchNat q z' s' => pure (p == q && (← convT z z') && (← convT s s'))
  | .call f as h, .call g bs h' => pure (h == h' && (← convT f g) && (← convTList as bs))
  | .succ a, .succ b | .fst a, .fst b | .snd a, .snd b | .ref a, .ref b => convT a b
  | .eq a b c, .eq d e f | .id a b c, .id d e f =>
    pure ((← convT a d) && (← convT b e) && (← convT c f))
  | .pi _ ds c, .pi _ ds' c' => pure ((← convTList ds ds') && (← convT c c'))
  | .fix _ _ ds c d b, .fix _ _ ds' c' d' b' =>
    pure (d == d' && (← convTList ds ds') && (← convT c c') && (← convT b b'))
  | .prim n as, .prim m bs => pure (n == m && (← convTList as bs))
  | .ctor t c _ ps as, .ctor u d _ qs bs => pure (t == u && c == d && (← convTList ps qs) && (← convTList as bs))
  | .tind n as, .tind m bs => pure (n == m && (← convTList as bs))
  | .matchInd p t as, .matchInd q u bs =>
    pure (p == q && t == u && (← convTList (as.map (·.2)) (bs.map (·.2))))
  | _, _ => pure false

/-- Two function values: compare their Π-types, their captured values, and the
observations of their generic calls, run from one shared generic environment. A
comparison that needs itself again (a recursive function stuck at its own generic
call observes only a sealed call of itself) answers "not convertible": sound, and
incomplete only for functions whose observation mentions themselves. -/
partial def convFn (f g : Value) : M Bool := do
  let mode := (← get).cfg.closureConv
  if mode == 1 then return false
  if (← get).convStack.contains (f, g) then return false
  let pf ← funType f none
  let pg ← funType g none
  unless ← conv pf pg do return false
  let caps : Value → List Value := fun | .clo cs _ => cs | _ => []
  if mode == 0 then
    unless ← convList (caps f) (caps g) do return false
  let .tPi cs (.pi hs ds _) := pf | return false
  onCopy do
    modify fun s => { s with env := #[{}], convStack := (f, g) :: s.convStack }
    pushFrame
    for v in cs do pushBind ⟨"κ"⟩ none v
    let mut args := #[]
    for (d, h) in ds.zip hs do
      let A ← evalType d
      let w ← match A with
        | .tRef T =>
          let σ ← freshAbs T
          let l ← freshLoan
          modifyFrame 0 fun fr => { fr with binds := fr.binds.push ⟨⟨s!"{h.name}°"⟩, some T, .loan l, false⟩ }
          pure (Value.borrow l (.abs σ))
        | _ => if ← isPropV A then pure Value.proof else pure (Value.abs (← freshAbs A))
      pushBind h (some A) w
      args := args.push w
    discard popFrameRaw
    -- D38 (v1.8): a borrow result is observed as its content, after one shared fresh
    -- value is written through it, so the owners show where it points
    let σw? ← match pf with
      | .tPi _ (.pi _ _ (.ref _)) =>
        if (← get).cfg.obsBorrow then
          match ← callType pf args (args.map fun _ => none) with
          | .tRef T => some <$> freshAbs T
          | _ => pure none
        else pure none
      | _ => pure none
    let obs (fv : Value) : M (Value × List Value) := onCopy do
      let (r, _) ← callFn false fv none args (args.map fun _ => none) false
      match r, σw? with
      | .borrow k u, some σw =>
        pushTemp u
        pushTemp (.borrow k (.abs σw))
        endAll
        discard popTemp
        let u' ← popTemp
        pure (u', (← get).env[0]!.binds.toList.map (·.val))
      | _, _ =>
        pushTemp r
        endAll
        let r ← popTemp
        pure (r, (← get).env[0]!.binds.toList.map (·.val))
    let (rf, cf) ← obs f
    let (rg, cg) ← obs g
    if mode == 2 then conv rf rg      -- counterfactual: compare the result only (breaker-fresh F3)
    else pure ((← conv rf rg) && (← convList cf cg))

/-- `Eq` computes (§4): reflexivity (decided by conversion) is `True`; two values built by
the same constructor give the conjunction of the equations between their fields, at the
field types instantiated at the parameters (v2.1, D52: injectivity; `S` is `Nat`'s
constructor with one field; no fields: `True`); distinct constructors of one type are
`False` (v2.0, D47). Proofs are all `⋆`, so an equation between proofs is reflexive. -/
partial def mkEqM (A a b : Value) : M Value := do
  if ← conv a b then return vTrue
  let cfg := (← get).cfg
  match a, b with
  | .succ a', .succ b' => if cfg.injective then return ← mkEqM .tNat a' b'
  | .ind t c _ ps fs, .ind u d _ qs gs =>
    if cfg.injective && t == u && c == d && fs.length == gs.length then
      -- the field types at the parameters: the equation's type `D(ā)`, else the values' own
      let args? := match A with
        | .tInd n as => if n == t then some as else none
        | _ => none
      let args? := args?.orElse fun _ =>
        if !ps.isEmpty then some ps else if !qs.isEmpty then some qs else none
      if let some args := args? then
        let Ts ← fieldTypes (← lookupInd t) args c
        if Ts.length == fs.length then
          let eqs ← ((Ts.map (·.2)).zip (fs.zip gs)).mapM fun (T, (v, w)) => mkEqM T v w
          return andList eqs
  | _, _ => pure ()
  if cfg.disjoint && distinctCtors a b then pure vFalse
  else pure (.tEq A a b)

-- ### Evaluation

partial def expectTy (what : String) (T : Option Value) (A : Value) : M Unit := do
  if let some T := T then
    unless ← conv T A do err s!"{what} has type {T}, expected {A}"

/-- P2 (v1.3, D26): erased terms leave no trace. A term whose type is a proposition is
evaluated on a private copy of Ω, argument evaluation included, and the copy is
discarded. Every value of a proposition is `⋆` (C7) and only such terms evaluate to
`⋆`, so this is decided on the value, in both modes. -/
partial def eval (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  let before := (← get).env
  let start := (← get).effects.size
  let f0 := before.size - 1
  let n0 := before[f0]!.binds.size
  let r ← evalCore typed t hint
  -- D28 (v1.5): whether this term is erased is decided syntactically and by declared
  -- classes, never from a normal form. Calls: the callee's class (set by `callFn`);
  -- sequencing forms inherit their tail's; proof formers are erased; an ascription is
  -- erased when its declared type is a proposition.
  -- A place, constant, value or λ that holds a proof is erased (finding P1): with the
  -- tail rule above, a sequencing form whose type has sort Prop is then erased on every
  -- path, as the block path requires (v1.7: a block of sort Prop is erased).
  -- v1.7 (D35): a sequencing form is erased iff it is a proof, i.e. its tail is one (a
  -- tail returning types is erased itself but does not make its context a proof).
  let cfg := (← get).cfg
  let (erased, proof) ← if cfg.erasureByDecl then
      match t with
      | .call _ _ _ => getFlags      -- set by `callFn` from the callee's class
      | .seq _ _ | .letIn _ _ _ | .matchNat _ _ _ | .matchInd _ _ _ =>
        let (e, p) ← getFlags
        pure (if cfg.seqByProof then (p, p) else (e, p))
      | .cong _ _ | .prim "trans" _ | .prim "symm" _ => pure (true, true)
      | .ctor ty _ _ _ _ => let p ← ctorIsProof ty; pure (p, p)   -- D42: a Prop inductive's value is a proof
      | .prim "J" [_, _, _, P, _, _] =>
        let p ← jErased P      -- the appendix's clause 4: the motive is syntactically into Prop
        pure (p, p)
      | .ascribe (.val .proof) _ => pure (true, true)
      | .ascribe _ A =>
        if cfg.seqByProof then
          -- a proof if the ascribed term is, or if the annotation's declared sort is Prop
          let top := (← get).env.size - 1
          let sc ← ((← get).env[top]!.binds.toList.reverse).mapM fun b => declOfVal b.val
          let p := (← getFlags).2 || (← propDecl sc A)
          pure (p, p)
        else
          let e := (← get).lastErased || (r.2.isSome && (← typeClass r.2.get!) == 2)
          pure (e, e)
      | .place _ | .const _ | .val _ | .fix .. =>
        let p ← match cfg.leafRule with
          | 0 => pure false
          | 1 => pure (r.1 == .proof)     -- finding P1's first fix: unstable (finding P3)
          | _ => leafProof t r.1
        pure (p, p)
      | _ => pure (false, false)
    else do let e ← erasedValue r.1; pure (e, e)   -- the v1.4 reading: decided on the value (breaker-fresh F1)
  -- D41 (v1.9): an erased run is confined, judged by the outermost erased term around
  -- it (a proof may mutate its own locals); a non-erased context rejects what is pending
  if cfg.confine then
    if erased then settleErased start f0 n0 else flushPending start
  if erased && (← get).cfg.eraseOnCopy then
    modify fun s => { s with env := before }
  setFlags (erased, proof)
  pure r

/-- The erasure class of a function type (D28, D35): 1 = it returns types, 2 = it
returns proofs, 0 = it returns data. v1.7: read off the codomain *term*, for top-level
and local functions alike: types if it is syntactically a sort, proofs if its declared
sort is `Prop` (`propDecl`), never by evaluating it (formal-appendix BoomL). The
function of a stuck block (codomain `.val B`, the match's type) returns proofs if `B`
has sort `Prop` and data otherwise, so the block is erased exactly when its match is
(BoomB). Cached per Π-type. -/
partial def fnClass (piTy : Value) : M Nat := do
  match (← get).classCache.lookup piTy with
  | some k => return k
  | none => pure ()
  let cfg := (← get).cfg
  let k ← match piTy with
    | .tPi cs (.pi hs ds c) =>
      match c with
      | .sort _ => pure 1
      | .val B => match cfg.blockRule with   -- a stuck block's function (`closeOffMatch`)
        | 0 => typeClass B                     -- v1.6: the call rule on its computed codomain
        | 1 => pure (if (← typeClass B) == 2 then 2 else 0)
        | _ => pure 0                          -- the class is given at the block's call
      | _ =>
        if cfg.classBySyntax then
          let sc := (ds.map declOfDom).reverse ++ (← cs.reverse.mapM declOfVal)
          pure (if ← propDecl sc c then 2 else 0)
        else match isPropTerm? c with   -- v1.6: evaluate the codomain at the generic call
          | some true => pure 2
          | some false => pure 0
          | none => onCopy do
            pushFrame
            for v in cs do pushBind ⟨"κ"⟩ none v
            for (d, h) in ds.zip hs do
              let A ← evalType d
              pushBind h (some A) (← genericValue A)
            typeClass (← evalType c)
    | _ => pure 0
  modify fun s => { s with classCache := (piTy, k) :: s.classCache }
  pure k

/-- What a captured value says about the variable holding it (see `declOfDom`): 1 = it
is a proposition, 2 = it is a function whose declared codomain is `Prop`. Read off the
value's constructor or its declared type, never by normalising. -/
partial def declOfVal (v : Value) : M Nat := do
  if (← typeClass v) == 2 then return 1
  let T? ← match v with
    | .gfn n => pure (some (← lookupGlobal n).ty)
    | .clo cs (.fix _ hs ds c _ _) => pure (some (Value.tPi cs (.pi hs ds c)))
    | .abs σ => some <$> absType σ
    | _ => pure none
  match T? with
  | some (.tPi _ (.pi _ _ c)) => pure (if isPropSort c then 2 else 0)
  | _ => pure 0

/-- v1.7 (D35): does the codomain term `c` have declared sort `Prop`, i.e. is its type
`Prop` when it is typed from the declared types of its heads, without normalising it?
`sc` gives, per de Bruijn index, what the variable's declared type says (`declOfDom`). -/
partial def propDecl (sc : List Nat) (c : Term) : M Bool := do
  match c with
  | .id .. | .eq .. => pure true
  | .tind n _ => pure (((← get).inds.find? (·.name == n)).map (·.sort) == some 0)   -- a Prop inductive (v2.0)
  | .pi _ ds c' => propDecl ((ds.map declOfDom).reverse ++ sc) c'   -- impredicative
  | .place (.var i) => pure (sc.getD i 0 == 1)
  | .const n => pure ((← lookupGlobal n).ty == .sort 0)
  | .call f _ _ => pure ((← headDecl sc f) == 2)
  | .letIn _ u w => propDecl ((← localDecl sc u) :: sc) w
  | .seq _ w => propDecl sc w
  | .matchNat _ z s => pure ((← propDecl sc z) || (← propDecl sc s))
  | .matchInd _ _ arms => arms.anyM fun (_, a) => propDecl sc a
  | .ascribe u A => pure (isPropSort A || (← propDecl sc u))
  | _ => pure false      -- an embedded value is not declared (a stuck block's parameter types)

/-- v1.7 (D35): which parameters are proofs, i.e. declared of sort Prop (`propDecl` on
the domain term, in the scope of the captured values and the earlier parameters). The
same flags wherever parameters are bound: the body, [Def] and [Call-type]. -/
partial def paramFlags (cs : List Value) (ds : List Term) : M (List Bool) := do
  if (← get).cfg.leafRule != 2 then return ds.map fun _ => false
  let quick : Term → Bool := fun
    | .nat | .unit | .ref _ | .sort _ | .tind "Pair" _ => true
    | _ => false
  if ds.all quick then return ds.map fun _ => false
  let capSc ← cs.reverse.mapM declOfVal
  let mut out := #[]
  let mut pre : List Nat := []     -- the earlier parameters, newest first
  for d in ds do
    out := out.push (← if quick d then pure false else propDecl (pre ++ capSc) d)
    pre := declOfDom d :: pre
  pure out.toList

/-- Is this leaf (a place, constant or `λ`) a proof, i.e. declared of sort Prop? A
variable by its binding's flag (`letIn`, `paramFlags`); a constructor field by its
declared type (v2.0: a parameter declared `: Prop`, or a Prop inductive); other
sub-places and captured values never are. -/
partial def leafProof (t : Term) (v : Value) : M Bool := do
  match t with
  | .place (.var i) => match ← varPos i with
    | .bind f j => pure (← get).env[f]!.binds[j]!.proof
    | _ => pure false
  | .place (.field g _) => fieldIsProof g      -- v2.0: a field declared of a proposition
  | .const n => pure ((← typeClass (← lookupGlobal n).ty) == 2)
  | .fix .. => match v with
    | .proof => pure true
    | .clo cs (.fix _ hs ds c _ _) => pure ((← fnClass (.tPi cs (.pi hs ds c))) == 2)
    | _ => pure false
  | _ => pure false

/-- What the declared type of a function term (a call's head) says (`declOfDom`). -/
partial def headDecl (sc : List Nat) (f : Term) : M Nat := do
  match f with
  | .place (.var i) => pure (sc.getD i 0)
  | .const n => declOfVal (.gfn n)
  | .fix _ _ _ c _ _ => pure (if isPropSort c then 2 else 0)
  | .val v => declOfVal v
  | .ascribe _ A => pure (declOfDom A)
  | _ => pure 0

/-- What the declared type of `let x = u` says about `x`. -/
partial def localDecl (sc : List Nat) (u : Term) : M Nat := do
  if ← propDecl sc u then return 1
  headDecl sc u

/-- The class of a declared type: a sort (its inhabitants are types), a proposition
(its inhabitants are proofs), or data. Read off the type's constructor or, for a
sealed type, off its head call's declared codomain; never by normalising further. -/
partial def typeClass (T : Value) : M Nat := do
  match T with
  | .sort _ => pure 1
  | .tEq .. => pure 2
  | .tInd n _ => pure (if (← lookupInd n).sort == 0 then 2 else 0)
  | .tPi _ _ => pure (if (← fnClass T) == 2 then 2 else 0)
  | .sealed t => pure (if (← sealedSort? t) == some 0 then 2 else 0)
  | .abs σ => match ← absType σ with
    | .sort 0 => pure 2
    | _ => pure 0
  | _ => pure 0

/-- `J(A, a, b, P, h, t)` is a proof when the motive returns propositions. -/
partial def jErased (P : Term) : M Bool := do
  match P with
  | .fix _ _ _ c _ _ => pure (c matches .sort 0)
  | _ => pure false

/-- Is this the value of an erased term: a proof (`⋆`) or a type? Types are values of
terms whose type is a sort (P2 erases them too): the type formers, sorts, a sealed
program whose sort is known, and an abstract value whose type is a sort. -/
partial def erasedValue (v : Value) : M Bool := do
  match v with
  | .proof | .tNat | .tUnit | .tEq .. | .tInd .. | .tRef _ | .tPi .. | .sort _ =>
    pure true
  | .sealed t => pure (← sealedSort? t).isSome
  | .abs σ => match ← absType σ with
    | .sort _ => pure true
    | _ => pure false
  | _ => pure false

/-- `hint`: the type the context requires of `t`, used only to infer the parameters of a
constructor application that its fields do not determine (v2.0, D46). -/
partial def evalCore (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  tick
  let ty (T : Value) : Option Value := if typed then some T else none
  match t with
  | .place p =>
    let T ← if typed then some <$> placeType p else pure none
    pure (← readPlace p, T)
  | .borrow p =>
    let T ← if typed then some <$> placeType p else pure none
    if let some T := T then
      if T.typeHasRef then err s!"&{← ppPlace p}: a borrow of a borrow-typed place"
    pure (← borrowPlace p, T.map .tRef)
  | .assign p u =>
    let (v, Tv) ← eval typed u
    if typed then expectTy "the assigned value" Tv (← placeType p)
    assignPlace p v
    pure (.unit, ty .tUnit)
  | .letIn h u w =>
    let (v, T) ← eval typed u
    pushBind h T v (← getFlags).2     -- `h` is a proof iff `u` is
    let (r, R) ← eval typed w
    let fl ← getFlags     -- the body's erasure flags (dropping may normalise)
    pushTemp r
    dropTopBind
    setFlags fl
    pure (← popTemp, R)
  | .seq u w =>
    let (v, _) ← eval typed u
    dropValue v
    eval typed w
  | .matchNat p z s => evalMatch typed p z s
  | .matchInd p ty arms => evalMatchInd typed p ty arms
  | .tind n as => evalTInd typed n as
  | .ctor ty c h ps as => evalCtor typed ty c h ps as hint
  | .const n =>
    let g ← lookupGlobal n
    let v ← if (← get).cfg.p5 && (← isPropV g.ty) then pure .proof else pure g.val
    pure (v, some g.ty)
  | .val v =>
    if typed then pure (v, some (← valType v)) else pure (v, none)
  | .sort l => pure (.sort l, some (.sort (l + 1)))
  | .pi _ ds c =>
    borrowParamCheck ds c
    -- a type former is erased: even its captures (which access places) run on a copy
    let (cs, t') ← onCopy (capture t)
    let T := Value.tPi cs t'
    if typed then pure (T, some (.sort (← sortOf T))) else pure (T, none)
  | .fix _ hs ds c _ _ =>
    borrowParamCheck ds c
    let (cs, t') ← capture t
    let v := Value.clo cs t'
    let T := match t' with
      | .fix _ _ ds' c' _ _ => Value.tPi cs (.pi hs ds' c')
      | _ => Value.tPi cs (.pi hs ds c)
    if typed then checkFix v cs t'
    let v ← if (← get).cfg.p5 && (← isPropV T) then pure .proof else pure v
    pure (v, some T)
  | .call f as hd => evalCall typed f as hd
  | .nat => pure (.tNat, some (.sort 1))
  | .unit => pure (.tUnit, some (.sort 1))
  | .zero => pure (.zero, ty .tNat)
  | .tt => pure (.unit, ty .tUnit)
  | .succ u =>
    let (v, T) ← eval typed u
    expectTy "the argument of S" T .tNat
    pure (.succ v, ty .tNat)
  | .fst u | .snd u =>
    -- `t.1`, `t.2` of a term that is not a place: field 1 or 2 of a pair (D52)
    let (v, T) ← eval typed u
    let first := t matches .fst _
    let r ← match v with
      | .ind "Pair" 0 _ _ [a, b] => pure (if first then a else b)
      | .abs _ | .sealed _ => if typed then err "projection of a neutral pair (no neutral projections in v1)" else stuckNow
      | _ => err s!"projection of a non-pair {v}"
    let R := match T with
      | some (.tInd "Pair" [A, B]) => some (if first then A else B)
      | _ => none
    pure (r, R)
  | .eq A a b => onCopy do
    let A' ← evalType A
    let (va, Ta) ← eval typed a
    let (vb, Tb) ← eval typed b
    expectTy "the left side of Eq" Ta A'
    expectTy "the right side of Eq" Tb A'
    pure (← mkEqM A' va vb, some (.sort 0))
  | .cong f h =>
    let (fv, fT) ← eval typed f
    let (_, Th) ← eval typed h
    if !typed then return (.proof, none)
    match Th.map unitTop with
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    | some (.tEq A a b) =>
      let (fa, B) ← callFn true fv fT #[a] #[some A] false
      let (fb, _) ← callFn true fv fT #[b] #[some A] false
      pure (.proof, some (← mkEqM B.get! fa fb))
    | some T => err s!"cong: the proof has type {T}, which is not an equation"
    | none => err "cong: untyped proof"
  | .ref A =>
    let A' ← evalType A
    if A'.typeHasRef then err "&A needs A borrow-free (RULES §1)"
    -- D48 (1): only data is borrowed, so `&A : Type₀` cannot make Type₀ impredicative
    if (← get).cfg.refData && !(← isDataType A') then
      err s!"[D48] &{A'}: only data types are borrowed (Nat, Unit, ×, an inductive type in Type), never a universe, a Π-type or a proposition"
    pure (.tRef A', some (.sort 1))
  | .id A a b => pure (← idType typed A a b, some (.sort 0))
  | .prim "J" [A, a, b, P, h, u] =>
    -- J(A, a, b, P, h, t) : P(b) for h : Eq A a b and t : P(a) (endpoints explicit, D23)
    if !typed then return (← eval false u)
    let A' ← evalType A
    let (av, Ta) ← confinedCopy "J's endpoint" (eval true a)
    let (bv, Tb) ← confinedCopy "J's endpoint" (eval true b)
    expectTy "J's first endpoint" Ta A'
    expectTy "J's second endpoint" Tb A'
    let (Pv, PT) ← eval true P
    let (_, Th) ← eval true h
    expectTy "J's equation" Th (← mkEqM A' av bv)
    let (v, Tu) ← eval true u
    let fl ← getFlags
    let (Pa, _) ← callFn true Pv PT #[av] #[some A'] false
    expectTy "the transported term" Tu Pa
    let (Pb, _) ← callFn true Pv PT #[bv] #[some A'] false
    setFlags fl    -- t's flags (J is t)
    pure (v, some Pb)
  | .prim "symm" [h] =>
    let (_, Th) ← eval typed h
    match Th.map unitTop with
    | some (.tEq A a b) => pure (.proof, some (← mkEqM A b a))
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    | _ => if typed then err "symm: not an equation" else pure (.proof, none)
  | .prim "trans" [h, k] =>
    let (_, Th) ← eval typed h
    let (_, Tk) ← eval typed k
    if !typed then return (.proof, none)
    match Th.map unitTop, Tk.map unitTop with
    | some (.tInd "True" []), some T | some T, some (.tInd "True" []) => pure (.proof, some T)
    | some (.tEq A a b), some (.tEq A' b' c) =>
      unless (← conv A A') && (← conv b b') do err s!"trans: {Th.get!} and {Tk.get!} do not compose"
      pure (.proof, some (← mkEqM A a c))
    | _, _ => err "trans: not equations"
  | .prim n _ => err s!"unknown primitive {n}"
  | .ascribe (.val .proof) A =>     -- a captured proof, inlined with its type (`capture`)
    if typed then pure (.proof, some (← evalType A)) else pure (.proof, none)
  | .ascribe u A =>
    if !typed then return (← eval false u)
    let A' ← evalType A
    let (v, T) ← match u with
      | .matchNat p z s => evalMatch true p z s (some A')
      | .matchInd p ty arms => evalMatchInd true p ty arms (some A')
      | _ => eval true u (some A')      -- the annotation is a hint for a constructor's parameters
    let fl ← getFlags
    expectTy "the ascribed term" T A'
    setFlags fl
    pure (v, some A')

/-- `D(ā)` (v2.0, D46): the arguments stand in type positions, so each is evaluated on a
private copy, confined (P2); when typed, each is checked against its parameter's type,
evaluated with the earlier parameters bound. Its sort is the declared one. -/
partial def evalTInd (typed : Bool) (n : String) (as : List Term) : M (Value × Option Value) := do
  let d ← lookupInd n
  if as.length != d.params.length then
    err s!"{n} takes {d.params.length} parameters, given {as.length}"
  let (vs, tys) ← evalParams n as typed
  if typed then checkParams d n vs tys
  pure (mkTInd n vs.toList (← get).cfg.unitNorm, if typed then some (.sort d.sort) else none)

/-- Parameters are type positions: each on a private copy, confined (P2). -/
partial def evalParams (n : String) (as : List Term) (typed : Bool) :
    M (Array Value × Array (Option Value)) := do
  let mut vs := #[]
  let mut tys := #[]
  for a in as do
    let (v, T) ← confinedCopy s!"a parameter of {n}" (eval typed a)
    vs := vs.push v
    tys := tys.push T
  pure (vs, tys)

/-- Each parameter against its declared type, evaluated with the earlier ones bound; no
borrow types (no borrows inside data). -/
partial def checkParams (d : IndDecl) (n : String) (vs : Array Value) (tys : Array (Option Value)) : M Unit :=
  onCopy do
    pushFrame
    for (((h, PT), v), T) in (d.params.zip vs.toList).zip tys.toList do
      let A ← evalType PT
      expectTy s!"the parameter {h.name} of {n}" T A
      noBorrowParam n v
      pushBind h (some A) v

/-- No borrows inside data (RULES §1), also through a parameter: `List(&Nat)` is not a type. -/
partial def noBorrowParam (n : String) (v : Value) : M Unit := do
  if v.typeHasRef then err s!"{n} at {v}: no borrows inside data (a parameter may not be a borrow type)"

/-- A constructor application `C(ā; t₁, …, tₖ)` of `D` (v2.0, D49 (4): the parameters `ā`
lead, surface `C[ā](t̄)`, and may be omitted). Its value is `C(ā; v̄)`, recording the
parameters when known, or `⋆` when `D` is a Prop inductive (D42). When typed, omitted
parameters are inferred from the fields' types, and those no field determines from
`hint` (the type the context requires: an annotation, the goal, a parameter or field
type). An untyped run records the parameters only when they are written. -/
partial def evalCtor (typed : Bool) (ty : String) (c : Nat) (h : Hint) (pts : List Term) (as : List Term)
    (hint : Option Value) : M (Value × Option Value) := do
  let d ← lookupInd ty
  let some (_, fields) := d.ctors[c]? | err s!"{ty} has no constructor {c}"
  if fields.length != as.length then err s!"{h.name} takes {fields.length} fields, given {as.length}"
  let np := d.params.length
  if !pts.isEmpty && pts.length != np then err s!"{h.name} takes {np} parameters, given {pts.length}"
  let (evs, etys) ← evalParams ty pts typed
  if typed && !pts.isEmpty then checkParams d ty evs etys
  let mut sol : Array (Option Value) := if !pts.isEmpty then evs.map some else match hint with
    | some (.tInd m ps) => if m == ty && ps.length == np then (ps.map some).toArray else Array.replicate np none
    | _ => Array.replicate np none
  let mut tys := #[]
  for (a, (_, FT)) in as.zip fields do
    let fh ← if typed && np > 0 && (a matches .ctor ..) then fieldTypeAt d sol FT else pure none
    let (w, T) ← eval typed a fh
    if let some T := T then sol := unifyParams np FT T sol
    tys := tys.push T
    pushTemp w
  let ws ← popTemps as.length
  let proof ← ctorIsProof ty
  if !typed then
    return (if proof then .proof else .ind ty c h evs.toList ws.toList, none)
  let mut ps := #[]
  for (s, (ph, _)) in sol.toList.zip d.params do
    match s with
    | some p => noBorrowParam ty p; ps := ps.push p
    | none => err s!"cannot infer the parameter {ph.name} of {h.name}: write it, {h.name}[…](…), or annotate, ({h.name}(…) : {ty}(…))"
  for (T, (fname, FT)) in tys.toList.zip (← fieldTypes d ps.toList c) do
    expectTy s!"field {fname} of {h.name}" T FT
  let v := if proof then Value.proof else .ind ty c h ps.toList ws.toList
  pure (v, some (mkTInd ty ps.toList (← get).cfg.unitNorm))

-- ### Calls: [Call], P5, [Call-type], [Close], [Rec]

partial def evalCall (typed : Bool) (f : Term) (as : List Term) (head : Bool)
    (cls? : Option Nat := none) : M (Value × Option Value) := do
  let (fv, fT) ← eval typed f
  pushTemp fv
  let mut tys := #[]
  let mut argSteps : Array (Nat × Nat) := #[]   -- D41: the borrows and moves that evaluate arguments
  let mut ws0 := #[]
  for a in as do
    let s := (← get).effects.size
    -- v2.0: a constructor argument's parameters may come from the parameter's type
    let hint ← if typed && (a matches .ctor ..) then argHint fv fT ws0 else pure none
    let (w, T) ← eval typed a hint
    if a matches .borrow _ | .place _ then argSteps := argSteps.push (s, (← get).effects.size)
    pushTemp w
    ws0 := ws0.push w
    tys := tys.push T
  let ws ← popTemps as.length
  let fv ← popTemp
  let r ← callFn typed fv fT ws tys head cls?
  -- D41: passing an outer place to an erased call is allowed
  if (← getFlags).1 && !argSteps.isEmpty then
    modify fun s => { s with effects := (s.effects.zipIdx.filter fun (_, k) =>
      !argSteps.any fun (a, b) => a ≤ k && k < b).map (·.1) }
  pure r

/-- The type of the next parameter of `fv`, with the earlier ones bound to the arguments
evaluated so far (a hint for a constructor argument's parameters; `none` if unknown). -/
partial def argHint (fv : Value) (fT : Option Value) (ws : Array Value) : M (Option Value) :=
  tryCatch (do
      let .tPi cs (.pi hs ds _) ← funType fv fT | return none
      let some d := ds[ws.size]? | return none
      onCopy do
        pushFrame
        for v in cs do pushBind ⟨"κ"⟩ none v
        for ((d', h), w) in (ds.zip hs).zip ws.toList do
          pushBind h (some (← evalType d')) w
        some <$> evalType d)
    fun _ => pure none

/-- The Π-type of a function value. -/
partial def funType (fv : Value) (fT : Option Value) : M Value := do
  if let some T := fT then return T
  match fv with
  | .gfn n => pure (← lookupGlobal n).ty
  | .clo cs (.fix _ hs ds c _ _) => pure (.tPi cs (.pi hs ds c))
  | .abs σ => absType σ
  | .sealed _ => err s!"the type of the sealed function {fv} is not known here (a call of a sealed function in untyped code)"
  | _ => err s!"{fv} is not a function"

partial def kindOf (B : Value) : M Kind := do
  if ← isPropV B then return .prop
  match B with
  | .tUnit => pure .unit
  | .tRef _ => pure .ref
  | _ => pure .data

/-- The row of [Close]'s table (and whether P5 applies), syntactically when possible. -/
partial def resultKind (piTy : Value) (ws : Array Value) : M Kind := do
  match piTy with
  | .tPi _ (.pi _ _ c) =>
    match c with
    | .val B => kindOf B
    | _ => match syntacticKind? c with
      | some k => pure k
      | none => kindOf (← callType piTy ws (ws.map fun _ => none))
  | _ => err s!"not a function type: {piTy}"

/-- [Close]'s row read from the declared codomain `B` (v1.7, D35): syntactically `Unit`,
`&T`, or anything else. A stuck block's codomain is the match's type. -/
partial def declKind (piTy : Value) : M Kind := do
  match piTy with
  | .tPi _ (.pi _ _ c) => match c with
    | .unit => pure .unit
    | .ref _ => pure .ref
    | .val B => do let k ← kindOf B; pure (if k == .prop then .data else k)
    | _ => pure .data
  | _ => err s!"not a function type: {piTy}"

/-- [Call-type]: the result type is `B` evaluated at the call point (after the
arguments are evaluated) with each parameter bound to its argument's value (a borrow
argument moved into it). The other free variables of `B` were captured when the
Π-type was formed. Each argument is checked against its parameter's type. -/
partial def callType (piTy : Value) (ws : Array Value) (tys : Array (Option Value)) : M Value := do
  let .tPi cs (.pi hs ds c) := piTy | err s!"not a function type: {piTy}"
  if ds.length != ws.size then err s!"arity: {ds.length} parameters, {ws.size} arguments"
  let pf ← paramFlags cs ds
  onCopy do
    pushFrame
    for v in cs do pushBind ⟨"κ"⟩ none v
    for ((d, h), i) in (ds.zip hs).zipIdx do
      let A ← evalType d
      expectTy s!"argument {i + 1} ({h.name})" tys[i]! A
      pushBind h (some A) ws[i]! (pf.getD i false)
    evalType c

/-- P5: the borrow arguments of a call that is not run end unchanged. -/
partial def endBorrowArgs (ws : Array Value) : M Unit := do
  for w in ws do
    if let .borrow l _ := w then
      pushTemp w
      endBorrow l
      discard popTemp

partial def fixOf (fv : Value) : M (List Value × Term) := do
  match fv with
  | .gfn n => match (← lookupGlobal n).fn? with
    | some t => pure ([], t)
    | none => err s!"{n} is not a function"
  | .clo cs t => pure (cs, t)
  | _ => err s!"{fv} is not a function"

/-- [Call]: push a frame `[caps, self, x̄ ↦ w̄]`, run the body, pop the frame. -/
partial def runBody (fv : Value) (cs : List Value) (t : Term) (ws : Array Value) : M Value := do
  let .fix self hs ds _ _ body := t | err "internal: not a fix"
  let d := (← get).depth
  if d ≥ 2000 then err "call depth exceeded (a non-terminating recursion)"
  modify fun s => { s with depth := d + 1 }
  let pf ← paramFlags cs ds
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  pushBind self none fv
  for ((h, w), p) in (hs.zip ws.toList).zip pf do pushBind h none w p
  let es := (← get).effects.size
  let (v, _) ← eval false body
  pushTempAt ((← topIdx) - 1) v
  popFrame
  -- the body's steps are rooted in its own frame, which is gone
  modify fun s => { s with depth := d, effects := s.effects.extract 0 es }
  popTemp

partial def callFn (typed : Bool) (fv : Value) (fT : Option Value) (ws : Array Value)
    (tys : Array (Option Value)) (head : Bool) (cls? : Option Nat := none) :
    M (Value × Option Value) := do
  if (← get).cfg.argNotBot then
    if let some i := ws.findIdx? (· == .bot) then
      err s!"[Call] argument {i + 1} is ⊥ at the call point (a later argument ended its borrow): an argument not of the parameter's type"
  -- A proof value is only ever called at a proposition: P5, not run.
  if fv == .proof then
    let B ← if typed then some <$> callType (← funType fv fT) ws tys else pure none
    endBorrowArgs ws
    setFlags (true, true)
    return (.proof, B)
  let piTy ← funType fv fT
  let B ← if typed then some <$> callType piTy ws tys else pure none
  if typed then
    trace fun _ => s!"[Call-type] {fv}({", ".intercalate (ws.toList.map toString)}) : {B.getD .bot}"
    recCheck fv ws
  -- [Close]'s row: v1.7 (D35) from the declared codomain; v1.6 from the computed type
  let byDecl := (← get).cfg.erasureByDecl
  let kind ← if byDecl && (← get).cfg.rowByDecl then declKind piTy else
    match B with
    | some B => kindOf B
    | none => resultKind piTy ws
  -- D28, D35: the callee's class, read off its declared codomain (a stuck block's is
  -- given by `closeOffMatch`)
  let cls ← match cls? with
    | some k => pure k
    | none => if byDecl then fnClass piTy else pure (if kind == .prop then 2 else 0)
  let kind := if byDecl && kind == .prop then Kind.data else kind
  if cls == 2 && (← get).cfg.p5 then
    endBorrowArgs ws
    setFlags (true, true)
    return (.proof, B)
  let r ← match fv with
    | .abs _ | .sealed _ =>
      -- a neutral head closes off at once (v1.3), except as [Seal]'s head call (D39)
      if head && (← get).cfg.headGuardNeutral then stuckNow else closeCall fv ws kind
    | .gfn _ | .clo _ _ =>
      let (cs, t) ← fixOf fv
      tryCatch (runBody fv cs t ws) fun e =>
        match e with
        | .stuck fu =>
          if head then throw e
          else do
            modify fun s => { s with fuel := fu }
            closeCall fv ws kind
        | .error m => throw (.error m)
    | _ => err s!"call of {fv}, which is not a function"
  let r := if cls == 2 then Value.proof else r
  setFlags (byDecl && cls != 0, byDecl && cls == 2)
  pure (r, B)

/-- [Close]: the call `f(w̄)` has a stuck body; the partial run has been discarded (the
state is back at the call point). `L := let cᵢ = uᵢ`, `C := f(ā)` with `aᵢ = &cᵢ` for
the borrow arguments `wᵢ = borrow_ℓᵢ uᵢ`; the result and the loans follow the table. -/
partial def closeCall (fv : Value) (ws : Array Value) (kind : Kind) : M Value := do
  -- Precondition (v1.1): every argument's content is loan-free (guaranteed by [Access]).
  -- An assertion: a violation is a bug of the rules or of this checker, never a user error.
  -- (Skipped in the counterfactual run without D19, which models the rules without it.)
  if (← get).cfg.accessInside then
   for w in ws do
     let u := match w with | .borrow _ u => u | u => u
     unless (liveLoansIn (← get).env u).isEmpty do
      err s!"INTERNAL [Close] precondition violated: the argument {w} holds a live loan (please report)"
  let bs : List (Nat × Nat × Value) := (ws.toList.zipIdx).filterMap fun (w, i) =>
    match w with
    | .borrow l u => some (i, l, u)
    | _ => none
  let m := bs.length
  let argT (d : Nat) (i : Nat) : Term :=
    match bs.findIdx? (·.1 == i) with
    | some j => .borrow (.var (d + m - 1 - j))
    | none => .val ws[i]!
  let C (d : Nat) : Term := .call (.val fv) ((List.range ws.size).map (argT d)) true
  let wrapL (body : Term) : Term :=
    (bs.zipIdx).foldr (fun ((_, _, u), j) acc => .letIn ⟨s!"c{j + 1}"⟩ (.val u) acc) body
  let cell (d j : Nat) : Term := .place (.var (d + m - 1 - j))
  match kind with
  | .ref =>
    let k ← freshLoan
    for ((_, l, _), j) in bs.zipIdx do
      let fill := wrapL (.letIn ⟨"r"⟩ (C 0) (.seq (.assign (.deref (.var 0)) (.val (.loan k))) (cell 1 j)))
      substEnv (.loan l) (← canonNeutral (.sealed fill)) false
    pure (.borrow k (← canonNeutral (.sealed (wrapL (.letIn ⟨"r"⟩ (C 0) (.place (.deref (.var 0))))))))
  | _ =>
    for ((_, l, _), j) in bs.zipIdx do
      substEnv (.loan l) (← canonNeutral (.sealed (wrapL (.seq (C 0) (cell 0 j))))) false
    if kind == .unit then pure .unit else canonNeutral (.sealed (wrapL (C 0)))

/-- [Rec]: at a recursive call, a parameter position survives if its argument (the
content, through a borrow) is a strict subterm of that parameter's entry value as
refined so far. The recursive position is any position that survives every call.
Every enclosing function being checked is considered, so a recursive call inside a
nested closure is checked against the outer function's entry values (fix L3). -/
partial def recCheck (fv : Value) (ws : Array Value) : M Unit := do
  let st ← get
  if !st.cfg.recGuard then return
  let mut candss := #[]
  for (ctx, cands) in st.recStack.zip st.recCands do
    if ctx.fn == fv then
      let cands' := cands.filter fun j =>
        match ctx.entries[j]?.join, ws[j]? with
        | some σ, some w =>
          let u := match w with | .borrow _ u => u | u => u
          (strictSubterms (expandRefs st.refs (.abs σ))).contains u
        | _, _ => false
      -- fail at the offending call, before it is run (running it may not terminate)
      if cands.isEmpty then
        err s!"[Rec] {fv} calls itself but declares no decreasing parameter (`by x`)"
      if cands'.isEmpty then
        err s!"[Rec] at {fv}({", ".intercalate (ws.toList.map toString)}): the argument in the decreasing position is not a strict subterm of that parameter's entry value as refined so far"
      candss := candss.push cands'
    else candss := candss.push cands
  set { st with recCands := candss.toList }

-- ### Match: [Match], [Split], stuck blocks

/-- Apply a refinement `σ := r` to Ω, the stored types and the goal ([Split]). -/
partial def refine (σ : Nat) (r : Value) : M Unit := do
  substEnv (.abs σ) r true
  modify fun s => { s with refs := (σ, r) :: s.refs }
  if (← get).neutrals.any (·.2 == σ) then renormAll

partial def evalMatch (typed : Bool) (p : Place) (z s : Term) (expected : Option Value := none) :
    M (Value × Option Value) := do
  accessPath p
  accessNeutralHead p
  let v ← content p
  match v with
  | .zero => eval typed z
  | .succ _ => eval typed s
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ => if typed then splitThenClose p z s σ expected else stuckNow
  | .sealed _ | .loan _ =>
    if !typed then stuckNow
    else
      let σ ← generalizeNeutral p v
      let expected ← expected.mapM (substV v (.abs σ))
      splitThenClose p z s σ expected
  | _ => err s!"[Match] on a non-Nat value {v}"

/-- [Split] on a neutral that is not an abstract value (a sealed program left by an
opaque call, deriver-e346 §E4.3): generalise first, i.e. replace every occurrence of it
(Ω, stored types, goal) by a fresh `σ`, then split on it (v1.2, D22). -/
partial def generalizeNeutral (p : Place) (n : Value) : M Nat := do
  unless (← get).cfg.generalize do
    err s!"[Split] on {← ppPlace p}, whose content {n} is a neutral but not an abstract value (RULES §5 splits only on σ)"
  -- v1.8: σ has the matched place's type (v1.6: the head's closed codomain, else Nat)
  let T ← if (← get).cfg.genPlaceType then placeType p else match n with
    | .sealed t => match ← sealedResultType? t with
      | some T => pure T
      | none => pure .tNat
    | _ => pure .tNat
  let σ ← freshAbs T
  trace fun _ => s!"[Split] generalise {n} to σ{σ} : {T}"
  substEnv n (.abs σ) true
  if (← get).cfg.genConsistent then
    modify fun s => { s with neutrals := (n, σ) :: s.neutrals }
  pure σ

/-- The type of a sealed program in result form, from its head's declared codomain
when that is closed (no dependency on the arguments). -/
partial def sealedResultType? (t : Term) : M (Option Value) := do
  let rec body : Term → Term
    | .letIn _ _ u => body u
    | u => u
  match body t with
  | .call (.val f) _ true =>
    match f with
    | .gfn n => match (← lookupGlobal n).ty with
      | .tPi _ (.pi _ _ c) => if c.freeVars.isEmpty then pure (some (← evalType c)) else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Finding G1: a neutral that a [Split] generalised stays generalised when normalisation
derives it again (it is a closed, deterministic computation, so every derivation of it
denotes the same value). Returns its refined value if it is one. -/
partial def canonNeutral (v : Value) : M Value := do
  if !(← get).cfg.genConsistent then return v
  match v with
  | .sealed _ => match (← get).neutrals.lookup v with
    | some σ => pure (expandRefs (← get).refs (.abs σ))
    | none => pure v
  | _ => pure v

/-- Re-normalise every sealed program in the state (after a generalised neutral has been
refined, sealed programs whose runs derive it may now make progress). -/
partial def renormAll : M Unit := do
  for p in allPos (← get).env do
    setAt p (← renormV (← getAt p))
  if let some g := (← get).goal then
    let g' ← renormV g
    modify fun s => { s with goal := some g' }
  let f := (← get).env.size
  for fi in [0:f] do
    let n := (← get).env[fi]!.binds.size
    for i in [0:n] do
      if let some T := (← get).env[fi]!.binds[i]!.ty then
        let T' ← renormV T
        modifyFrame fi fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }

partial def renormV (v : Value) : M Value := do
  if !(v.anyAtom fun | .sealed _ => true | _ => false) then return v
  match v with
  | .sealed t => do
    let t' ← renormT t
    canonNeutral (← nfSealed t')
  | .succ w => return .succ (← renormV w)
  | .borrow l w => return .borrow l (← renormV w)
  | .ind ty c h ps fs => return .ind ty c h ps (← fs.mapM renormV)
  | .tEq A a b => mkEqM (← renormV A) (← renormV a) (← renormV b)
  | .tInd n as => return mkTInd n (← as.mapM renormV) (← get).cfg.unitNorm
  | _ => return v

partial def renormT (t : Term) : M Term := do
  match t with
  | .val v => return .val (← renormV v)
  | .letIn h a b => return .letIn h (← renormT a) (← renormT b)
  | .seq a b => return .seq (← renormT a) (← renormT b)
  | .assign p a => return .assign p (← renormT a)
  | .call f as hd => return .call (← renormT f) (← as.mapM renormT) hd
  | _ => return t

/-- [Split] for a non-tail match: check each arm under its refinement, then close the
match off as a stuck block and continue once from the unrefined state (D15). The
block's type is the arms' common type, or the annotation `let x : T = match …`
(each arm is then checked against `T` refined, v1.2 D22). -/
partial def splitThenClose (p : Place) (z s : Term) (σ : Nat) (expected : Option Value) :
    M (Value × Option Value) := do
  splitArmsThenClose (Term.matchNat p z s) σ
    [(pure .zero, z), (do pure (.succ (.abs (← freshAbs .tNat))), s)] expected

/-- The general form: one arm per constructor, each checked under the refinement its
builder produces (fresh abstract values for the fields), then close off. -/
partial def splitArmsThenClose (mt : Term) (σ : Nat) (arms : List (M Value × Term))
    (expected : Option Value) : M (Value × Option Value) := do
  let fvs := mt.freeVars
  let before ← fvs.mapM fun o => do getAt (← varPos o)
  let saved ← get
  let mut tys : Array Value := #[]
  let mut moved : List Nat := []
  let mut allProof := true
  let mut violation : Option String := none     -- D41: an arm with an outer effect
  let mut pending : Array Effect := #[]           -- D41: the arms' pending steps, judged after the block
  let f0 := (← get).env.size - 1
  let n0 := (← get).env[f0]!.binds.size
  for (mk, arm) in arms do
    let r ← mk
    refine σ r
    let es := (← get).effects.size
    let (_, T) ← eval true arm
    allProof := allProof && (← getFlags).2
    let armEs := (← get).effects
    pending := pending ++ (armEs.extract es armEs.size).filter (·.pending)
    if violation.isNone then
      violation ← confinementViolation es f0 n0 "an arm of an erased stuck block"
    let some T := T | err "internal: untyped arm"
    if let some E := expected then
      let E' ← substV (.abs σ) r E
      unless ← conv T E' do
        err s!"an arm of the annotated match has type {T}, but the annotation refined to this arm is {E'}"
    for (o, b) in fvs.zip before do
      let v ← getAt (← varPos o)
      if v == .bot && b != .bot && !moved.contains o then moved := moved ++ [o]
    restoreKeep saved
    tys := tys.push T
  let B ← match expected with
    | some E => pure E
    | none =>
      let some T0 := tys[0]? | err "internal: a match with no arms"
      for T in tys do
        unless ← conv T T0 do
          err s!"the arms of a non-tail match have different types ({T0} and {T}); annotate it (let x : T = match …)"
      pure T0
  let r ← closeOffMatch mt B moved allProof
  modify fun s => { s with effects := s.effects ++ pending }
  -- D41: an erased block's run is one of its arms, so each arm must be confined
  if (← getFlags).1 && (← get).cfg.confine && (← get).cfg.confineBodies then
    if let some m := violation then err m
  pure r

/-- The refinement of `σ` to constructor `c` of an inductive type at parameters `ps`:
fresh abstract values for its fields, of the fields' types; a field that is a proof
gets `⋆` (as a proof parameter does, D27). -/
partial def ctorRefinement (d : IndDecl) (ps : List Value) (c : Nat) : M Value := do
  let (cn, _) := d.ctors[c]!
  let mut fs := #[]
  for (_, T) in ← fieldTypes d ps c do fs := fs.push (← genericValue T)
  pure (.ind d.name c ⟨cn⟩ ps fs.toList)

/-- The inductive type of a matched place and its parameters, from the place's type (the
arms' constructors name `ty`; `""` for a match with no arms). The type is read, not
assumed from the arms (finding: v1.9's checker split a `T(n)`-typed place with `L`'s
constructors, so `f(1, x)`, with `T(1) = Nat`, ran `L`'s arms on a number). -/
partial def scrutType (p : Place) (ty : String) : M (IndDecl × List Value) := do
  if ty != "" && !(← get).cfg.scrutTyped then
    let d ← lookupInd ty
    if d.params.isEmpty && d.sort == 1 then return (d, [])   -- counterfactual: v1.9 assumed it
  match ← placeType p with
  | .tInd n ps =>
    if ty != "" && n != ty then err s!"[Match] on {← ppPlace p} : {mkTInd n ps}, with the constructors of {ty}"
    pure (← lookupInd n, ps)
  | T => err s!"[Match] on {← ppPlace p}, whose type {T} is not an inductive type{if ty == "And" then " (And(True, P) ≡ P: match on the conjunct instead)" else ""}"

/-- D45 (v2.0): a match on a proof (the arms' constructors are those of a Prop inductive),
or with no arms, is by the scrutinee's *type*: its content (`⋆`, or an abstract value) is
never inspected, so the decision is the same on every path. No constructors: no arms, any
result type (the annotation's), erased and unreachable (its value is `⋆`). One: its arm,
the fields being places holding `⋆`. Several: each arm is checked and each must be a proof,
so the match is a proof, `⋆` (it cannot pick an arm). Subsingleton elimination: unless
the type has no constructors or one whose fields are all propositions, every arm must be
a proof (the declared reading of "its result is a proposition", D42). -/
partial def evalMatchByType (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term))
    (expected : Option Value) : M (Value × Option Value) := do
  accessPath p
  let v ← content p
  if v == .bot then err s!"[Match] on {← ppPlace p}, which was moved out"
  if arms.isEmpty then
    if typed then
      let (d, _) ← scrutType p ty
      unless d.ctors.isEmpty do err s!"a match with no arms on {← ppPlace p} : {d.name}, which has constructors"
      if expected.isNone then err "annotate a match with no arms outside tail position (let x : T = match p {})"
    setFlags (true, true)
    return (.proof, expected)
  let d ← lookupInd ty
  let ps ← if typed then (·.2) <$> scrutType p ty else pure []
  let large ← largeElim d
  let needProof := typed && (← get).cfg.subsingleton && !large
  let subErr : M Unit := err (subsingletonMsg d)
  -- a constructor value is seen only when Prop values are not erased (counterfactual D42)
  if let .ind _ c _ _ _ := v then
    match arms[c]? with
    | some (_, a) => return ← eval typed a
    | none => err s!"[Match] no arm for constructor {c}"
  -- D49 (2): a match on a proof of a non-subsingleton is erased (its checked arms are all
  -- proofs), so a run does not run it: its value is ⋆ (read from the declaration)
  if !typed && !large && (← get).cfg.subsingleton then
    setFlags (true, true)
    return (.proof, none)
  if let [(_, a)] := arms then
    let a ← if typed then bindDataFields p d ps 0 a else pure a
    let r ← eval typed a
    if needProof && !(← getFlags).2 then subErr
    return r
  if !typed then
    -- counterfactual (no subsingleton elimination): an erased match is ⋆, otherwise no
    -- arm can be chosen and the match is stuck
    let saved ← get
    discard (eval false arms[0]!.2)
    let pf := (← getFlags).2
    restoreKeep saved
    if pf then setFlags (true, true); return (.proof, none)
    stuckNow
  let saved ← get
  let mut tys := #[]
  let mut allProof := true
  let mut pending : Array Effect := #[]
  for ((_, a0), c) in arms.zipIdx do
    let a ← bindDataFields p d ps c a0
    let es := (← get).effects.size
    let (_, T) ← eval true a
    allProof := allProof && (← getFlags).2
    let armEs := (← get).effects
    pending := pending ++ (armEs.extract es armEs.size).filter (·.pending)
    let some T := T | err "internal: untyped arm"
    if let some E := expected then
      unless ← conv T E do err s!"an arm of the annotated match has type {T}, but the annotation is {E}"
    tys := tys.push T
    restoreKeep saved
  modify fun s => { s with effects := s.effects ++ pending }
  let B ← match expected with
    | some E => pure E
    | none =>
      let T0 := tys[0]!
      for T in tys do
        unless ← conv T T0 do err s!"the arms of a match on a proof have different types ({T0} and {T}); annotate it"
      pure T0
  if !allProof then
    if (← get).cfg.subsingleton then subErr
    return ← closeOffMatch (.matchInd p ty arms) B [] false   -- counterfactual: stuck
  setFlags (true, true)
  pure (.proof, some B)

/-- [Match] / [Split] on a declared inductive type. -/
partial def evalMatchInd (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term))
    (expected : Option Value := none) : M (Value × Option Value) := do
  if ← byTypeMatch ty arms then return ← evalMatchByType typed p ty arms expected
  accessPath p
  accessNeutralHead p
  let v ← content p
  match v with
  | .ind t c _ _ _ =>
    if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
    match arms[c]? with
    | some (_, a) => eval typed a
    | none => err s!"[Match] no arm for constructor {c}"
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ =>
    if !typed then stuckNow
    else
      let (d, ps) ← scrutType p ty
      splitArmsThenClose (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement d ps c, a)) expected
  | .sealed _ | .loan _ =>
    if !typed then stuckNow
    else
      let (d, ps) ← scrutType p ty
      let σ ← generalizeNeutral p v
      let expected ← expected.mapM (substV v (.abs σ))
      splitArmsThenClose (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement d ps c, a)) expected
  | _ => err s!"[Match] on {v}, which is not a value of {ty}"

/-- Place `q` is a prefix of place `p` (both rooted in the same frame). -/
partial def placePrefix (q p : Place) : Bool :=
  let (i, qs) := q.steps
  let (j, ps) := p.steps
  i == j && qs.length ≤ ps.length && ps.take qs.length == qs

/-- Stuck blocks (RULES §3, v1.3): close a stuck match off as a call to an anonymous
function of its free places, captured as Rust infers closure captures, on maximal place
prefixes: a place some arm moves out of is moved in; otherwise a place written or
borrowed (under `&_` or left of `:=`) in some arm is passed as `&`; otherwise a place
read is copied. A borrow variable read as a whole is a move (reading a borrow moves it);
assigning a borrow variable as a whole moves it too (passing `&x` would be `&&T`). -/
partial def closeOffMatch (mt : Term) (B : Value) (moved : List Nat) (allProof : Bool) :
    M (Value × Option Value) := do
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
  -- the free places used, re-rooted at the frame index, with their capture mode
  -- (0 = copy, 1 = &, 2 = move)
  let scrut : Option Place := match mt with
    | .matchNat sp _ _ | .matchInd sp _ _ => some sp
    | _ => none
  let mut uses : Array (Place × Nat) := #[]
  for (o, p, k) in mt.freeOccs do
    let q := p.mapRoot fun _ => .var o
    -- counterfactual D32: a write through a pattern variable (a strict extension of the
    -- block's scrutinee by `.1`) is not seen as a use of the scrutinee's place
    if !(← get).cfg.patternWritesVisible && (k == .borrow || k == .assign) then
      if let some sp := scrut then
        if placePrefix sp q && !(sp == q) then continue
    let b := (← get).env[f]!.binds[nb - 1 - o]!
    let whole := q matches .var _
    let isBorrowVar := b.val.isBorrow || (b.ty matches some (.tRef _))
    let mode :=
      if whole && isBorrowVar && (k == .read || k == .assign) then 2
      else if whole && moved.contains o then 2
      else if k == .borrow || k == .assign then 1
      else 0
    uses := uses.push (q, mode)
  -- maximal prefixes: places with no strict prefix among the used places
  let mut caps : Array (Place × Nat) := #[]
  for (q, _) in uses do
    let hasPrefix := uses.any fun (q', _) => placePrefix q' q && !(q' == q)
    if !hasPrefix && !(caps.any fun (c, _) => c == q) then
      let mode := (uses.filter fun (p, _) => placePrefix q p).foldl (fun m (_, k) => max m k) 0
      caps := caps.push (q, mode)
  -- order the captures by frame position (oldest binding first), then by path
  let capsS := caps.qsort fun (a, _) (b, _) => a.root > b.root || (a.root == b.root && (a.steps.2.length < b.steps.2.length))
  let n := capsS.size
  let mut hints := #[]
  let mut doms := #[]
  let mut args := #[]
  let mut pflags := #[]
  for (q, mode) in capsS do
    let T ← placeType q
    -- a captured proof variable stays a proof in the block: its parameter is declared
    -- `: T` with `T : Prop` (v1.7: the same flag on the direct and the block path)
    let env := (← get).env
    pflags := pflags.push (← match q with
      | .var o => pure (mode != 1 && env[f]!.binds[nb - 1 - o]!.proof)
      | .field g _ => do pure (mode != 1 && (← fieldIsProof g))   -- v2.0: a proof field (declared)
      | _ => pure false)
    hints := hints.push (Hint.mk ((← ppPlace q).replace "*" "" |>.replace "(" "" |>.replace ")" "" |>.replace "." "_"))
    match mode with
    | 2 =>
      if !((← get).cfg.blockMoves) && (T matches .tRef _) then
        -- counterfactual C5: reborrow instead of moving
        doms := doms.push T; args := args.push (Term.borrow (.deref q))
      else
        doms := doms.push T; args := args.push (Term.place q)
    | 1 => doms := doms.push (.tRef T); args := args.push (Term.borrow q)
    | _ => doms := doms.push T; args := args.push (Term.place q)
  let capsL := capsS.toList
  let body := mt.mapFreePlace (fun c p =>
    match capsL.zipIdx.find? fun ((q, _), _) => placePrefix q p with
    | some ((q, mode), k) =>
      let param := Place.var (c + n - 1 - k)
      let base := if mode == 1 then Place.deref param else param
      -- counterfactual C5: the moved-in borrow was reborrowed, so the parameter is the reborrow
      let (_, qs) := q.steps
      let (_, ps) := p.steps
      (ps.drop qs.length).foldl (fun acc st => match st with
        | .deref => .deref acc | .fst => .fst acc | .snd => .snd acc
        | .field g => .field g acc) base
    | none => p) 0
  let domTs := (doms.zip pflags).toList.map fun (T, p) =>
    if p then Term.ascribe (.val T) (.sort 0) else .val T
  let anon := Value.clo [] (.fix ⟨"_"⟩ hints.toList domTs (.val B) none body)
  trace fun _ => s!"[Stuck block] {anon}({", ".intercalate (args.toList.map (·.pp []))})"
  -- v1.7 (D35): the block is erased exactly when its match would be, i.e. at every
  -- instance: when every arm is a proof (finding P2: not read off the computed type B)
  let cfg := (← get).cfg
  let cls? := if cfg.erasureByDecl && cfg.blockRule == 2 then some (if allProof then 2 else 0) else none
  let (v, _) ← evalCall false (.val anon) args.toList false cls?
  -- counterfactual v1.6: a block erased by the call rule (returning types) erases its match
  if cfg.blockRule == 0 then
    let (e, _) ← getFlags
    setFlags (e, e)
  pure (v, some B)

-- ### Observation and `Id` (RULES §4)

/-- `⟦t⟧^W`: on a private copy of Ω, run `t`, end every borrow, and return the result
and the final contents of the owners in `W` (a tuple of the machine, not a `Pair` value,
D52). -/
partial def observe (typed : Bool) (t : Term) (A : Value) (W : List Pos) : M (Value × List Value) := onCopy do
  let es := (← get).effects.size
  let (v, T) ← eval typed t A      -- A: a hint for a constructor's parameters
  if (← get).cfg.confine then flushPending es   -- D41: a side of Id is not an erased context
  expectTy "a side of Id" T A
  pushTemp v
  endAll
  let v ← popTemp
  let ws ← W.mapM getAt
  pure (v, ws)

/-- `Id A t u ≡ And(Eq A r r', And(Eq T₁ w₁ w'₁, …))` over the result and the owners in
`W = W(t, u)` (just `Eq A r r'` when `W` is empty), both sides from the same Ω on
independent copies (v2.1, D52: directly, not through a pair, so `A` may be any borrow-free
type, a proposition or a universe included). -/
partial def idType (typed : Bool) (A t u : Term) : M Value := do
  let A' ← evalType A
  if A'.typeHasRef then err s!"Id at {A'}: A must be borrow-free (RULES §4)"
  let st ← get
  let W := footprint st.env [t, u] st.cfg.multiOwner
  let Ts ← W.mapM fun p => do
    match ← tyAt p with
    | some T => pure T
    | none => valType (← getAt p)
  let (a, as) ← observe typed t A' W
  let (b, bs) ← observe typed u A' W
  let eqs ← ((A', (a, b)) :: Ts.zip (as.zip bs)).mapM fun (T, (x, y)) => mkEqM T x y
  pure (andList eqs)

-- ### Typing: [Def], [Split] in tail position

/-- Check a term in tail position. At the end of every path, `k` gets the result and
its type (in that path's refined state). A match on an abstract `σ` here is split:
each arm is checked to the end under its refinement ([Split]). -/
partial def checkTail (t : Term) (k : Value → Value → M Unit) : M Unit := do
  match t with
  | .letIn h u w =>
    let es := (← get).effects.size
    let (v, T) ← eval true u
    flushPending es     -- D41: the tail judgement is not an erased context
    pushBind h T v (← getFlags).2
    checkTail w fun r R => do
      let fl ← getFlags      -- the path's tail flags (dropping may normalise)
      pushTemp r
      dropTopBind
      setFlags fl
      k (← popTemp) R
  | .seq u w =>
    let es := (← get).effects.size
    let (v, _) ← eval true u
    flushPending es
    dropValue v
    checkTail w k
  | .matchNat p z s =>
    accessPath p
    accessNeutralHead p
    match ← content p with
    | .zero => checkTail z k
    | .succ _ => checkTail s k
    | .abs σ =>
      let saved ← get
      refine σ .zero
      trace fun _ => s!"[Split] σ{σ} := 0"
      checkTail z k
      restoreKeep saved
      let σ' ← freshAbs .tNat
      refine σ (.succ (.abs σ'))
      trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
      checkTail s k
      restoreKeep saved
    | v@(.sealed _) | v@(.loan _) =>
      discard (generalizeNeutral p v)
      checkTail t k
    | _ =>
      let (v, T) ← eval true t
      k v T.get!
  | .matchInd p ty arms =>
    if ← byTypeMatch ty arms then
      -- D45 (v2.0): [Split] on a proof is by its type: each arm is checked, with the fields
      -- as places holding ⋆ and no refinement; no arms, no paths
      accessPath p
      let v ← content p
      if v == .bot then err s!"[Match] on {← ppPlace p}, which was moved out"
      let (d, ps) ← scrutType p ty
      if arms.isEmpty && !d.ctors.isEmpty then
        err s!"a match with no arms on {← ppPlace p} : {d.name}, which has constructors"
      let needProof := (← get).cfg.subsingleton && !(← largeElim d)
      let k' : Value → Value → M Unit := fun r R => do
        if needProof && !(← getFlags).2 then err (subsingletonMsg d)
        k r R
      match v with
      | .ind _ c _ _ _ => checkTail (arms[c]!).2 k'     -- counterfactual D42: a constructor value
      | _ =>
        let saved ← get
        for ((_, a), c) in arms.zipIdx do
          checkTail (← bindDataFields p d ps c a) k'     -- D49 (3)
          restoreKeep saved
      return
    accessPath p
    accessNeutralHead p
    match ← content p with
    | .ind t c _ _ _ =>
      if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
      match arms[c]? with
      | some (_, a) => checkTail a k
      | none => err s!"[Match] no arm for constructor {c}"
    | .abs σ =>
      let (d, ps) ← scrutType p ty
      let saved ← get
      for (c, (_, a)) in (List.range d.ctors.length).zip arms do
        let r ← ctorRefinement d ps c
        refine σ r
        trace fun _ => s!"[Split] σ{σ} := {r}"
        checkTail a k
        restoreKeep saved
    | v@(.sealed _) | v@(.loan _) =>
      discard (generalizeNeutral p v)
      checkTail t k
    | _ =>
      let (v, T) ← eval true t
      k v T.get!
  | _ =>
    let es := (← get).effects.size
    let (v, T) ← eval true t (← get).goal     -- the goal: a hint for a constructor's parameters
    flushPending es
    match T with
    | some T => k v T
    | none => err "internal: untyped result in the checker"

/-- [Def]: `fix f (x̄:Ā):B := b` is checked at its generic call. Ω has a fresh owned
place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ` (frame 0); the call is
`f(ā)` with `aᵢ = &cᵢ` or `σᵢ`; the goal is the [Call-type] of that call; the body
runs in a pushed frame and its result's type must convert to the goal as refined by
splits. Afterwards the whole state is restored. -/
partial def checkFix (fv : Value) (cs : List Value) (t : Term) : M Unit := do
  let .fix self hs ds c dec body := t | err "internal: not a fix"
  borrowParamCheck ds c
  let saved ← get
  -- D31 (v1.5): without `by`, f is not in scope in its body (a λ)
  if dec.isNone && (← get).cfg.unboundWithoutBy && (body.freeOccs.any (·.1 == ds.length)) then
    err s!"{self.name} is not in scope in its own body: it declares no decreasing parameter (`by x`), so it is not recursive (D31)"
  if (← get).cfg.selfHeadOnly then
    let n := ds.length
    unless headOnly (fun d p => p.root == d + n) 0 body do
      err s!"[Rec] {self.name} occurs in its own body other than as the head of a call (fix L1)"
  -- keep `refs` (refinements made on the way to a nested fix still hold) and the
  -- enclosing functions' [Rec] contexts
  modify fun s => { s with env := #[{}], goal := none }
  let pf ← paramFlags cs ds
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  let mut entries := #[]
  for ((d, h), p) in (ds.zip hs).zip pf do
    let A ← evalType d
    match A with
    | .tRef T =>
      let σ ← freshAbs T
      let l ← freshLoan
      modifyFrame 0 fun fr => { fr with binds := fr.binds.push ⟨⟨s!"{h.name}°"⟩, some T, .loan l, false⟩ }
      pushBind h (some A) (.borrow l (.abs σ)) p
      entries := entries.push (if T == .tNat || (T matches .tInd ..) then some σ else none)
    | _ =>
      if (← get).cfg.p5 && (← get).cfg.proofParamsStar && (← isPropV A) then
        pushBind h (some A) .proof p
        entries := entries.push none
      else
        let σ ← freshAbs A
        pushBind h (some A) (.abs σ) p
        entries := entries.push (if A == .tNat || (A matches .tInd ..) then some σ else none)
  let goal ← evalType c
  trace fun _ => s!"[Def] {self.name}: goal {goal}"
  let F1 ← popFrameRaw
  let piTy := Value.tPi cs (.pi hs ds c)
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  pushBind self (some piTy) fv
  for b in F1.binds.extract cs.length F1.binds.size do pushBind b.hint b.ty b.val b.proof
  -- [Rec]: the decreasing parameter is the one named by `by xⱼ` (v1.2, D23); without
  -- `by` the function is not recursive (no candidate survives a recursive call)
  let cands ← if (← get).cfg.inferRecPos then
      pure ((entries.toList.zipIdx).filterMap fun (e, i) => e.map fun _ => i)
    else match dec with
      | some j =>
        if (entries[j]?.join).isNone then
          err s!"`by {(hs.getD j ⟨"?"⟩).name}`: the decreasing parameter must have an inductive type (or be a borrow of one)"
        pure [j]
      | none => pure []
  if dec.isNone && !(← get).cfg.unboundWithoutBy then
    -- counterfactual D31 (the v1.3 literal reading): [Rec] constrains only `fix … by x`
    modify fun s => { s with goal := some goal }
  else if (← get).cfg.recNested then
    modify fun s => { s with goal := some goal, recStack := ⟨fv, entries⟩ :: s.recStack,
                              recCands := cands :: s.recCands }
  else  -- counterfactual L3: a nested function's check starts with a fresh [Rec] context
    modify fun s => { s with goal := some goal, recStack := [⟨fv, entries⟩], recCands := [cands] }
  -- D41: the body of a function whose calls are erased must be confined
  let bodyErased? ← if (← get).cfg.confine && (← get).cfg.confineBodies then
      if (← get).cfg.erasureByDecl then pure (some ((← fnClass piTy) != 0)) else pure none
    else pure (some false)
  let es := (← get).effects.size
  let bf := (← get).env.size - 1
  -- the parameters through which the body reaches its caller's places: borrow parameters
  -- (a by-value parameter, a capture or a local is the body's own)
  let outer : List Nat := ((← get).env[bf]!.binds.toList.zipIdx.filter fun (b, _) =>
    b.ty matches some (.tRef _)).map (·.2)
  checkTail body fun v T => do
    let erasedBody ← match bodyErased? with
      | some b => pure b
      | none => erasedValue v          -- the v1.4 reading: by the value
    if erasedBody then
      let es' := (← get).effects
      for e in es'.extract es es'.size do
        if e.f < bf || (e.f == bf && outer.contains e.i) then
          err s!"[D41+] the body of {self.name}, whose calls are erased, {e.desc}, a place of its caller (through a borrow parameter)"
    pushTempAt ((← topIdx) - 1) v
    popFrame
    discard popTemp
    let g := (← get).goal.getD .bot
    trace fun _ => s!"[Def] {self.name}: path ends with type {T} against goal {g}"
    unless ← conv T g do
      err s!"the body of {self.name} has type {T}, but the goal is {g}"
  restoreKeep saved
  unless (← get).cfg.recNested do
    modify fun s => { s with recCands := saved.recCands }

end

end Ochr
