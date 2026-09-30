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
  | .succ w | .ghost w => firstBorrowLabel w
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
  | .ghost v => .ghost (expandRefs refs v)
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

-- the machine is one `mutual` block, and compiling it (LCNF) outgrew the default heartbeats
set_option maxHeartbeats 1000000 in
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
  | .ghost w => return .ghost (← substV x r w)
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
          -- a type's sealed programs re-run as types: erased, reads copy (D53, fuzz-port RN)
          let T' ← withErased (substV x r T)
          modifyFrame f fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }
  if types then
    withErased do
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
  -- D53: a sealed program re-runs with runtime semantics (moves, ⊥ checks); only its final
  -- read of a cell (`peek`, closeCall's `K`) is an observation, and copies
  let r ← tryCatch (do let (v, _) ← eval false t; pure (some v)) fun e =>
    match e with
    | .stuck f _ => do modify (fun s => { s with fuel := f }); pure none
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
      -- D53 (h): moving out through a borrow is allowed if the content is whole again when
      -- the borrow ends
      -- D64 [Repack]: in the checked program, a borrow of a value of a dependent type ends
      -- with the value of its type again (a borrow parameter's, when the function returns)
      if (← get).typing then
        if let (.borrow _ _, some (.tRef A)) := (valAt env p, ← tyAt p) then
          repackCheck "a borrow of it ends" c A
      if c.hasHole then
        err s!"[D53] a borrow ends while its content is partly moved out ({c})"
      setAt p rest
      substEnv (.loan l) c false

/-- D64 [Repack]: at a whole-again point, a value holding values of dependent types must be
of its type `T` by their telescopes again (a borrow's content, for a borrow of `&A`). -/
partial def repackCheck (what : String) (v : Value) (T : Value) : M Unit := do
  if !(← get).cfg.repack then return
  let (v, T) := match v, T with
    | .borrow _ c, .tRef A => (c, A)
    | _, _ => (v, T)
  if !(← hasDependent v) then return
  fire .Repack fun _ => s!"{what}: {v} : {T}"
  if let some m ← packedErr v T then err s!"[Repack] {what}, but it is open: {m}"

/-- D64 [Repack] at a whole use of the place `p` (of type `T`): read, moved, borrowed, passed
or captured whole. A place moved out or ended is left to the machine's own error. -/
partial def repackAt (p : Place) (T : Value) (what : String) : M Unit := do
  let v ← tryCatch (content p) fun _ => pure .bot
  if v matches .bot | .ghost _ then return
  repackCheck s!"{← ppPlace p} is {what}" v T

/-- D64 [Open]: a write or borrow through an index field of a dependent constructor value
invalidates the proof fields whose types mention that field: they become `⊥` until assigned
again (a proof is `⋆` and carries no type, so a stale one could not be told apart at the
repack; an assigned proof is checked against the telescope at the current contents). -/
partial def openWrite (p : Place) : M Unit := do
  let rec prefixes : Place → List (Place × FieldRef)
    | .field g q => (q, g) :: prefixes q
    | .deref q | .fst q | .snd q => prefixes q
    | .var _ => []
  for (q, g) in prefixes p do
    let some d := (← get).inds.find? (·.name == g.ty) | continue
    unless (d.indexFields g.ctor).contains g.idx do continue
    for ((fname, FT), j) in ((d.ctors[g.ctor]!).2).zipIdx do
      if j != g.idx && (d.fieldRefs g.ctor FT).contains g.idx && (← fieldTermIsProp d FT) then
        let fp := Place.field ⟨g.ty, g.ctor, j, fname⟩ q
        if ← tryCatch (do discard (content fp); pure true) (fun _ => pure false) then
          fire .Open fun _ => s!"a write through {g.name} invalidates the proof field {fname}"
          setPlace fp .bot

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
  | l :: _ =>
    -- a loan that other owners hold too (a hole in several sealed fills: one of them is
    -- the borrow's real owner, which is not known) is released here only: the borrow
    -- becomes a ghost, unusable, still holding the others, so a [Drop] of another owner
    -- still errors (uncertainty never makes the symbolic path more permissive: Bad2)
    let env := (← get).env
    let here ← varPos p.root
    let others := (owners env l).filter (· != here)
    if (← get).cfg.ghostBorrows && !others.isEmpty then releaseHere p l
    else endBorrow l
    accessInside p
  | [] => pure ()

/-- Release `loan_l` in the place `p` only (its value is the borrow's current content) and
make the borrow a ghost ([Access] with several possible owners). -/
partial def releaseHere (p : Place) (l : Nat) : M Unit := do
  let env := (← get).env
  let some bp := findBorrow env l | endBorrow l
  let some (c, _) := (valAt env bp).takeBorrow l | endBorrow l
  let v ← content p
  setPlace p (← substV (.loan l) c v)
  setAt bp ((valAt (← get).env bp).ghostBorrow l)

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

/-- K2/K3: this point runs at runtime: not in an erased term, and not in model code (an
`implemented by` body or a model function's, which never runs at runtime). -/
partial def atRuntime : M Bool := do
  pure ((← get).erasedDepth == 0 && (← get).modelDepth == 0)

/-- K3: a match whose arms name the constructors of an abstract (or unsized) type, at runtime
outside model code. -/
partial def abstractMatchCheck (p : Place) (ty : String) : M Unit := do
  if ty == "" then return
  let d ← lookupInd ty
  if (d.abstract || d.unsized) && (← get).cfg.abstractTypes && (← atRuntime) then
    err s!"[K3] a match on {← ppPlace p} with the constructors of the abstract type {ty} at runtime, outside model code"

/-- A type headed by an `unsized` declaration (K2). -/
partial def isUnsizedType (T : Value) : M Bool := do
  match T with
  | .tInd n _ => tryCatch (do pure (← lookupInd n).unsized) (fun _ => pure false)
  | _ => pure false

/-- K2: at runtime outside model code, a place whose content has an unsized type is only
borrowed: never read, moved or assigned (matching it is K3's check). The type is read off
the content (a constructor value, or an abstract value's type). -/
partial def unsizedCheck (p : Place) (v : Value) (what : String) : M Unit := do
  if !(← get).cfg.unsizedTypes || !(← atRuntime) then return
  let T? ← match v with
    | .ind t _ _ ps _ => pure (some (Value.tInd t ps))
    | .abs σ => tryCatch (some <$> absType σ) (fun _ => pure none)
    | _ => pure none
  if let some T := T? then
    if ← isUnsizedType T then
      err s!"[K2] {← ppPlace p}, of the unsized type {T}, is {what} at runtime (outside model code a view is only borrowed)"

/-- K2/K3: a function is model code when it is `implemented by` native code, or a parameter
or its result has an unsized type by value (runtime code can never hold such a value). Read
from the declared types, syntactically (as D55 reads sorts): a type term headed by an unsized
declaration, directly or through type functions whose bodies are (`Slice(E, n)`). -/
partial def modelSignature (_hs : List Hint) (ds : List Term) (c : Term) : M Bool := do
  (c :: ds).anyM (unsizedTerm · 8)

/-- A type term headed by an unsized declaration, read off syntax: an inductive type, or a
call of a type function whose body is one (`fuel` bounds the unfolding). -/
partial def unsizedTerm (T : Term) (fuel : Nat) : M Bool := do
  match T with
  | .tind n _ => tryCatch (do pure (← lookupInd n).unsized) (fun _ => pure false)
  | .val v => isUnsizedType v
  | .call (.const f) _ _ =>
    if fuel == 0 then return false
    match ← tryCatch (do pure (← lookupGlobal f).fn?) (fun _ => pure none) with
    | some (.fix _ _ _ _ _ body) => unsizedTerm body (fuel - 1)
    | _ => pure false
  | _ => pure false

/-- [Read]: a borrow is moved out (`p ↦ ⊥`), in any term. Borrow-free content is copied
by an erased term (D53 (a)) and when its type is a copy type; otherwise a runtime read
moves it out, leaving a ghost that erased terms still read (D53 (c)). A place partly
moved out cannot be read at runtime (D53 (h)). -/
partial def readPlace (p : Place) : M Value := do
  accessPath p; accessInside p
  let v ← content p
  unsizedCheck p v "read"
  let cfg := (← get).cfg
  let erased := (← get).erasedDepth > 0
  let inPlace := (← get).inPlace
  if inPlace then modify fun s => { s with inPlace := false }
  match v with
  | .bot =>
    if let .field g _ := p then
      if (← lookupInd g.ty).dependent g.ctor && (← fieldIsProof g) then
        err s!"[Open] {← ppPlace p} is a proof field invalidated by a write to a field its type mentions: assign it a new proof first"
    err s!"[Read] {← ppPlace p} was moved out or its borrow ended (reading ⊥)"
  | .ghost w =>
    if erased && cfg.ghosts then return w.unghost
    err s!"[Read] {← ppPlace p} was moved out (D53)"
  | .borrow _ _ => logEffect p "moves"; setPlace p .bot; pure v
  | _ =>
    if v == .proof then return v
    if erased then return v.unghost
    -- read in place: not consumed, but it must be there (D53: a call's head, the Fn rule;
    -- a stuck block's read-only capture, as the match inspects its place)
    if inPlace then
      if v.hasHole then err s!"[Read] {← ppPlace p} was partly moved out (D53)"
      return v
    if v.hasHole then err s!"[Read] {← ppPlace p} was partly moved out (D53)"
    if ← copyRead p v then return v
    if cfg.fnRule && (← isCapture p) then
      err s!"[D53] a closure's body moves a captured value out ({← ppPlace p}); a closure may run again: clone it"
    logEffect p "moves"
    setPlace p (if cfg.ghosts then .ghost v else .bot)
    pure v

/-- D53: reading `p` (holding `v`) copies: its type is a copy type, or it holds a function
whose captures are copies (the Fn rule). -/
partial def copyRead (p : Place) (v : Value) : M Bool := do
  let T ← tryCatch (placeType p) (fun _ => pure .bot)
  isCopyValue T v

partial def isCopyValue (T : Value) (v : Value) : M Bool := do
  match T, v with
  | .tPi .., .gfn _ => pure (← get).cfg.fnRule
  | .tPi .., .clo cs _ =>
    if !(← get).cfg.fnRule then return false
    cs.allM fun c => do
      match c with
      | .proof | .tNat | .tUnit | .tRef _ | .tInd .. | .tEq .. | .tPi .. | .sort _ => pure true
      | _ => isCopyValue (← tryCatch (valType c) (fun _ => pure .bot)) c
  | _, _ => isCopyType T

/-- Is `p` rooted in a closure's captured value? -/
partial def isCapture (p : Place) : M Bool := do
  match ← varPos p.root with
  | .bind f i => pure (← get).env[f]!.binds[i]!.cap
  | _ => pure false

/-- A match's scrutinee: a match inspects its place in place (no move). A place moved out
(D53) can be matched only by an erased term, which sees its ghost. -/
partial def matchContent (p : Place) : M Value := do
  match ← content p with
  | .ghost w =>
    if (← get).erasedDepth > 0 && (← get).cfg.ghosts then pure w
    else err s!"[Match] on {← ppPlace p}, which was moved out"
  | v => pure v

/-- D41: record an assignment, borrow or move of `p` by its root position. -/
partial def logEffect (p : Place) (kind : String) : M Unit := do
  if let .bind f i ← varPos p.root then
    -- D53: moves and assignments by place, from which a stuck block's effect on what it
    -- captures is read (`armMoves`); a step through a local borrow is also the owner's
    if kind == "moves" || kind == "assigns" then
      let isMove := kind == "moves"
      modify fun s => { s with placeLog := s.placeLog.push (f, i, p, isMove) }
      if let some (i', ss) ← throughLocalBorrow f i p then
        modify fun s => { s with placeLog := s.placeLog.push (f, i', ss.foldl stepPlace (Place.var 0), isMove) }
    if (← get).cfg.confine then
      let root := (← get).env[f]!.binds[i]!.hint.name
      modify fun s => { s with effects := s.effects.push { f, i, kind, place := p, root } }

/-- One step added to a place. -/
partial def stepPlace (q : Place) : Step → Place
  | .deref => .deref q | .fst => .fst q | .snd => .snd q | .field g => .field g q

/-- Where `loan_l` sits inside a value, as steps from it. -/
partial def loanPath (v : Value) (l : Nat) : M (Option (List Step)) := do
  match v with
  | .loan m => pure (if m == l then some [] else none)
  | .succ w => pure ((← loanPath w l).map (Step.fst :: ·))
  | .borrow _ w => pure ((← loanPath w l).map (Step.deref :: ·))
  | .ind t c _ _ fs =>
    let names ← tryCatch (do
        let d ← lookupInd t
        pure ((d.ctors[c]?.map (·.2.map (·.1))).getD [])) fun _ => pure []
    for (w, i) in fs.zipIdx do
      if let some ss ← loanPath w l then
        return some (Step.field ⟨t, c, i, names.getD i s!"f{i}"⟩ :: ss)
    pure none
  | _ => pure none

/-- A place `*r…` through a borrow variable `r` whose loan sits in an older binding of the
same frame: that binding's index and the steps from it to the place (the owner's move). -/
partial def throughLocalBorrow (f i : Nat) (p : Place) : M (Option (Nat × List Step)) := do
  let (_, ss) := p.steps
  let .deref :: rest := ss | return none
  let .borrow l _ := (← get).env[f]!.binds[i]!.val | return none
  let binds := (← get).env[f]!.binds
  for j in [0:i] do
    if let some path ← loanPath binds[j]!.val l then
      return some (j, path ++ rest)
  pure none

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
partial def confinedCopy {α : Type} (what : String) (x : M α) : M α := onCopy <| withErased do
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
  | .bot | .ghost _ => err s!"[Borrow] {← ppPlace p} was moved out (borrowing ⊥)"
  | .borrow _ _ => err "[Borrow] a borrow of a borrow (&&T is outside the core)"
  | _ =>
    if v.hasHole then
      err s!"[Borrow] {← ppPlace p} was partly moved out (D53)"
    logEffect p "borrows"
    let l ← freshLoan
    setPlace p (.loan l)
    pure (.borrow l v)

/-- [Assign] with the value already computed: drop the old content, store the new. -/
partial def assignPlace (p : Place) (v : Value) : M Unit := do
  pushTemp v
  accessPath p; accessInside p
  let old ← content p
  unsizedCheck p old "assigned"
  match old with
  | .borrow l _ | .ghost (.borrow l _) => endBorrow l
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
  | .borrow l _ | .ghost (.borrow l _) => endBorrow l
  | v =>
    if !(liveLoansIn (← get).env v).isEmpty then
      err s!"[Drop] {b.hint.name} goes out of scope while it is borrowed"
  modifyFrame f fun fr => { fr with binds := fr.binds.pop }

/-- [Drop] a discarded value (`t; u`). -/
partial def dropValue (v : Value) : M Unit := do
  pushTemp v
  match v with
  | .borrow l _ | .ghost (.borrow l _) => endBorrow l
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
      let d ← lookupInd n
      if d.dependent g.ctor then return ← depFieldType d ps g q
      match (← fieldTypes d ps g.ctor)[g.idx]? with
      | some (_, T) => pure T
      | none => err s!"{← ppPlace q}.{g.name}: no such field"
    | T => err s!"{← ppPlace q}.{g.name}: no field at type {T}"

/-- D64: the fields of the constructor value a place holds, as a constructor `g` names it:
through a ghost (a moved value's fields are its ghosts) and through a loan (a place lent out
has its borrow's content). -/
partial def ctorFields (v : Value) (g : FieldRef) : M (Option (List Value)) := do
  match v with
  | .ind t c _ _ fs => pure (if t == g.ty && c == g.ctor then some fs else none)
  | .ghost w => pure ((← ctorFields w g).map (·.map .ghost))
  | .loan l =>
    let env := (← get).env
    match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
    | some (c, _) => ctorFields c g
    | none => pure none
  | _ => pure none

/-- D64, rule 2 and [Open]: the type of field `g` of the value at `q`, of the dependent
constructor `g.ctor` of `d` at parameters `ps`. Its type by the telescope is computed from
the earlier fields' current contents. A field whose declared type mentions no earlier field
has that type. Any other field has it while its content does (the value is packed);
otherwise the value is *open*, and the field is typed by its content's own type (what was
written into it, a stored type), until the value is repacked. -/
partial def depFieldType (d : IndDecl) (ps : List Value) (g : FieldRef) (q : Place) : M Value := do
  if !d.fieldDependent g.ctor g.idx then
    match ← fieldTypeAt d ((ps.map some).toArray) g.ctor g.idx [] with
    | some T => return T
    | none => err s!"{← ppPlace q}.{g.name}: no such field"
  let cv ← content q
  let some fs ← ctorFields cv g
    | err s!"{← ppPlace q}.{g.name}: its type depends on the earlier fields of {g.ty}, but {← ppPlace q} holds {cv}, not a value of its constructor (match on it first)"
  -- D64: a field's type from the earlier fields' contents
  let some (_, T) := (← fieldTypesOf d ps g.ctor fs (some (g.idx + 1)))[g.idx]?
    | err s!"{← ppPlace q}.{g.name}: no such field"
  if !d.fieldDependent g.ctor g.idx then return T
  let c := (fs.getD g.idx .bot).unghost
  if c == .bot || c == .proof then return T
  if (← packedErr c T).isNone then return T
  let S ← tryCatch (valType c) fun _ => pure T
  fire .Open fun _ => s!"{g.name} is open: typed by its content, {S}, not {T}"
  pure S

/-- D64 [Repack]: why `v` is not a value of `T` by the telescopes of the dependent
constructors inside it, or `none`. A constructor value is checked field by field against its
field types, computed from its own earlier fields and `T`'s parameters; a leaf by its own type
(an abstract value's stored type, a sealed program's, a proof against a proposition). A hole
(`⊥`, a ghost) is not packed. A constructor value with no dependent constructor inside whose
type is `T` needs no walk. -/
partial def packedErr (v : Value) (T : Value) : M (Option String) := do
  match v with
  | .ghost _ | .bot => pure (some s!"it holds {v} (moved out, or a proof invalidated by a write to a field its type mentions)")
  | .proof => pure (if ← isPropV T then none else some s!"a proof where {T} is expected")
  | .ind t c _ ps fs =>
    if !(← hasDependent v) && (← convVal v T) then return none
    let d ← lookupInd t
    let as? := match T with
      | .tInd n as => if n == t then some as else none
      | _ => none
    let as? := as?.orElse fun _ => if ps.length == d.params.length then some ps else none
    let some as := as? | return some s!"{v} is not of type {T}"
    if !ps.isEmpty && !(← convList ps as) then return some s!"{v} is not of type {T}"
    let tel ← fieldTypesOf d as c fs
    let cn := (d.ctors[c]!).1
    for (((f, Tf), fv), j) in (tel.zip fs).zipIdx do
      if let some m ← packedErr fv Tf then
        let own ← tryCatch (valType fv) (fun _ => pure .bot)
        return some (match fv with
          | .ind .. => s!"in field {f} of {cn}, {m}"
          | .ghost _ | .bot => s!"field {f} of {cn}: {m}"
          | _ =>
            if d.fieldDependent c j then
              s!"field {f} of {cn} holds a value of type {own}, but its type from the earlier fields is {Tf}"
            else s!"field {f} of {cn}: {m}")
    pure none
  | .abs σ =>
    let A ← absType σ
    pure (if ← conv A T then none else some s!"{v} : {A}, not {T}")
  | _ => pure (if ← convVal v T then none else some s!"{v} is not of type {T}")

/-- The type of a leaf value converts to `T` (a value whose type cannot be read does not). -/
partial def convVal (v : Value) (T : Value) : M Bool :=
  tryCatch (do conv (← valType v) T) fun _ => pure false

/-- D64 [Open]: `p` is a data field whose declared type mentions earlier fields (its
assignment is a strong update). -/
partial def strongUpdate (p : Place) : M Bool := do
  let .field g _ := p | return false
  let some d := (← get).inds.find? (·.name == g.ty) | return false
  pure (d.fieldDependent g.ctor g.idx && !(← fieldIsProof g))

/-- D64: does a value hold a value of a dependent constructor (outside sealed programs and
closures, which carry their types)? -/
partial def hasDependent (v : Value) : M Bool := do
  match v with
  | .ind t c _ _ fs =>
    if (← lookupInd t).dependent c then return true
    fs.anyM hasDependent
  | .ghost w | .borrow _ w | .succ w => hasDependent w
  | _ => pure false

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
  | .loan l =>
    -- a live loan's value is its borrow's content: a place lent out has that content's type
    let env := (← get).env
    match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
    | some (c, _) => valType c
    | none => err s!"cannot infer the type of the value {v}"
  | _ => err s!"cannot infer the type of the value {v}"

/-- The type of a sealed program (neutral data, e.g. a captured one): its term typed as
an ordinary term on a private copy, from the empty environment. Its head call is not
marked, so a stuck body closes off; its [Call-type] is what gives the type. -/
partial def sealedType (t : Term) : M Value := onCopy do
  modify fun s => { s with env := #[{}], recStack := [], goal := none }
  let (_, T) ← eval true t.unHead
  match T with
  | some T => pure T
  | none => err s!"cannot infer the type of the sealed program ⌈{t.pp []}⌉"

-- ### Inductive declarations (v2.0: D45–D47)

/-- The field types of constructor `c` of `d` at the parameters `ps` (D46), as a telescope
(D64, [Ind]): the declared field type terms are evaluated in order, in a frame binding the
parameters and the fields, field `j` bound to `val j Tⱼ` once its type `Tⱼ` is known (its
content, or a fresh generic value). A field not yet bound is `⊥`, which a well-formed
telescope never reads (a field type mentions only earlier fields). Only the first `upto`
fields are computed. Returns each field's name, type and bound value. The frame is pushed on
the real state, not a copy, so that the values `val` creates (fresh σ) survive. -/
partial def fieldTele (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value)
    (upto : Option Nat := none) : M (List (String × Value × Value)) := do
  let some (_, fields) := d.ctors[c]? | err s!"{d.name} has no constructor {c}"
  if ps.length != d.params.length then
    err s!"{d.name} takes {d.params.length} parameters, given {ps.length}"
  let fields := match upto with | some n => fields.take n | none => fields
  let k := (d.ctors[c]!).2.length
  pushFrame
  let r ← tryCatch (do
      -- the fields first (`var np …`), then the parameters (`var 0 …`), as resolved
      for i in [0:k] do pushBind ⟨((d.ctors[c]!).2[i]!).1⟩ none .bot
      for ((h, PT), v) in d.params.zip ps do
        let pd' ← withLive true (typeDecl false [] [] PT)
        pushBind h none v pd'.isProof pd'
      let top ← topIdx
      let mut out := #[]
      for ((f, FT), j) in fields.zipIdx do
        let T ← evalType FT
        let v ← val j T
        out := out.push (f, T, v)
        let p ← fieldTermIsProp d FT
        modifyFrame top fun fr => { fr with binds := fr.binds.modify j fun b =>
          { b with val := v, ty := some T, proof := p, decl := if p then .prop else .other } }
      pure out.toList) fun e => do discard popFrameRaw; throw e
  discard popFrameRaw
  pure r

/-- The field types of constructor `c` at the parameters `ps`, for a constructor with no
dependent field (D46); a dependent one needs its fields' values (`fieldTypesOf`). -/
partial def fieldTypes (d : IndDecl) (ps : List Value) (c : Nat) : M (List (String × Value)) := do
  if d.dependent c then err s!"internal: the field types of {d.name}'s constructor {c} depend on its fields"
  pure ((← fieldTele d ps c (fun _ _ => pure .bot)).map fun (f, T, _) => (f, T))

/-- D64: the field types of constructor `c` at the parameters `ps` and the field values
`fs` (rule 2: a field's type is computed from the earlier fields' contents). -/
partial def fieldTypesOf (d : IndDecl) (ps : List Value) (c : Nat) (fs : List Value)
    (upto : Option Nat := none) : M (List (String × Value)) := do
  pure ((← fieldTele d ps c (fun j _ => pure (fs.getD j .bot)) upto).map fun (f, T, _) => (f, T))

/-- D64: fresh generic values for the fields of constructor `c`, each of its type computed
from the earlier ones ([Ind] and [Split]: `σ := C(σ₁, σ₂)` with `σ₂ : T₂[σ₁]`); a proof
field is `⋆`. Returns each field's name, type and value. -/
partial def fieldsGeneric (d : IndDecl) (ps : List Value) (c : Nat) :
    M (List (String × Value × Value)) :=
  fieldTele d ps c fun _ T => genericValue T

/-- D53: a copy type, read off a type; a type not fully known is not one: `Unit`, a sort
(types are erased), a proposition (its values are `⋆`), an inductive declared `copy`
(`Word`), and an inductive in `Type₀` whose fields do not mention it and are copy types at
the parameters (`Bool`, a pair of copy types). Not `Nat`, not a recursive type, not a
function type (a closure is a copy by its captures: `isCopyValue`), not a neutral. -/
partial def isCopyType (T : Value) : M Bool := do
  if ← tryCatch (isPropV T) (fun _ => pure false) then return true   -- a proposition
  match T with
  | .tUnit | .sort _ | .tEq .. => pure true
  | .tInd n args =>
    let d ← lookupInd n
    if d.copy || d.sort == 0 then return true
    if d.ctors.any (fun (_, fs) => fs.any fun (_, FT) => FT.mentionsTInd n) then return false
    -- D64: a type with a dependent field is a copy type only when declared `copy` (its field
    -- types are not fixed by the parameters)
    if (List.range d.ctors.length).any d.dependent then return false
    for i in [0:d.ctors.length] do
      for (_, FT) in ← fieldTypes d args i do
        unless ← isCopyType FT do return false
    pure true
  | _ => pure false

/-- One declared field type, field `i` of constructor `c`, at partially known parameters and
the values of the fields before it (for a hint; unknown parameters and fields are bound to
`⊥`, which a field type not mentioning them never reads). -/
partial def fieldTypeAt (d : IndDecl) (sol : Array (Option Value)) (c i : Nat) (earlier : List Value) :
    M (Option Value) := do
  let np := d.params.length
  let some (_, fields) := d.ctors[c]? | return none
  let some (_, FT) := fields[i]? | return none
  let k := fields.length
  unless FT.freeVars.all fun j => (j < np && (sol[np - 1 - j]!).isSome) ||
      (np ≤ j && j < np + k && np + k - 1 - j < earlier.length) do return none
  tryCatch (onCopy do
      pushFrame
      for jj in [0:k] do pushBind ⟨(fields[jj]!).1⟩ none (earlier.getD jj .bot)
      for ((h, PT), v) in d.params.zip sol.toList do
        pushBind h none (v.getD .bot) false (← withLive true (typeDecl false [] [] PT))
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
  -- K4: a call of a function declared to return `Prop` (a proof field, `h : Sorted(xs)`)
  | .call (.const f) _ _ => match (← get).globals.find? (·.name == f) with
    | some g => pure (g.ty matches .tPi _ (.pi _ _ (.sort 0)))
    | none => pure false
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
  -- D64: a dependent constructor's fields are all bound, in order, each at its type from the
  -- earlier ones: data to fresh values, proofs to `⋆` at their types (whose type a later
  -- field's may read)
  let dep := d.dependent c
  let fts ← if dep then fieldsGeneric d ps c
    else pure ((← fieldTypes d ps c).map fun (f, T) => (f, T, Value.bot))
  let mut datas : Array (Nat × String × Value × Term) := #[]
  for (((fname, FT), (_, T, v)), i) in (fields.zip fts).zipIdx do
    if ← fieldTermIsProp d FT then
      if dep then datas := datas.push (i, fname, T, .ascribe (.val .proof) (.val T))
    else
      let g ← if dep then pure v else genericValue T
      datas := datas.push (i, fname, T, .val g)
  if datas.isEmpty then return arm
  let k := datas.size
  let fieldPlace (i : Nat) : Place := .field ⟨d.name, c, i, ""⟩ p
  let body := arm.mapFreePlace (fun dep q =>
    match datas.toList.zipIdx.find? fun ((i, _, _, _), _) => placePrefix (fieldPlace i) q with
    | some ((i, _, _, _), j) =>
      let (_, qs) := q.steps
      let (_, fs) := (fieldPlace i).steps
      (qs.drop fs.length).foldl (fun acc st => match st with
        | .deref => .deref acc | .fst => .fst acc | .snd => .snd acc
        | .field g => .field g acc) (Place.var (dep + k - 1 - j))
    | none => q.mapRoot fun r => .var (r + dep + k)) 0
  let mut t := body
  for (_, fname, _, u) in datas.toList.reverse do
    t := .letIn ⟨fname⟩ u t
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
    pushCaps cs
    let (pds, _) ← paramDecls cs hs ds c
    let mut l := 0
    for ((d, h), pd) in (ds.zip hs).zip pds do
      let A ← evalType d
      l := max l (← sortOf A)
      let gv ← genericValue A
      let pd' ← refineDecl pd (some A) gv
      pushBind h (some A) gv pd'.isProof pd'
    let lb ← sortOf (← evalType c)
    pure (if lb == 0 then 0 else max l lb)
  | _ => err s!"{T} is not a type"

-- ### Declared types (D55) and the erasure pre-pass

/-- What the declared type of a place says: a variable's, through a borrow the borrowed
type's, a constructor field's (a proof field is a proof). -/
partial def placeDecl (sc : List DeclInfo) : Place → M DeclInfo
  | .var i => do
    if h : i < sc.length then return sc[i]
    if (← get).liveScope then liveDecl (i - sc.length) else pure .other
  | .deref q => do
    match ← placeDecl sc q with
    | .ref d => pure d
    | _ => pure .other
  | .field g _ => do pure (if ← tryCatch (fieldIsProof g) (fun _ => pure false) then .prop else .other)
  | _ => pure .other

/-- Arms agree on what their declared type says (`any`, a zero-arm match, agrees with all).
Arms that are all proofs agree on a proof, whatever their shapes (a proof variable in one
arm, a function into proofs in another: applied, either is a proof). Arms of which some are
proofs and some not have no common declared type (`conflict`, D63): the paper's "a match has
each arm's" declared type is then undefined, and the match is rejected wherever its declared
type is read ([Type-pos], the erasure pre-pass). With `armsAgree` off (the earlier reading,
fuzz-port R9), such a match says nothing (`any`) and the arm that runs decides. -/
partial def agreeDecl (armsAgree : Bool) (ds : List DeclInfo) : DeclInfo :=
  if armsAgree && ds.contains .conflict then .conflict else
  match ds.filter (· != .any) with
  | [] => .any
  | d :: rest =>
    if rest.all (· == d) then d
    else if (d :: rest).all DeclInfo.isProof then .prop
    else if (d :: rest).any DeclInfo.isProof then (if armsAgree then .conflict else .any)
    else .other

/-- The error for a term with no declared type (D63). -/
partial def conflictMsg (t : Term) (ns : List String) : String :=
  s!"[D63] the arms of a match in {t.pp ns} disagree about being proofs (some are, some are not), so it has no declared type"

/-- The declared type of a term, read from the declared types of its heads without
normalising (the D35 notion), in a scope saying what each variable's declared type says
(de Bruijn order; `ns` names them, for messages). With `chk`, every type position inside
the term is checked to have a sort as its declared type (D55); without, only the spine
that decides the result is read (the pre-pass at evaluation). -/
partial def declOf (chk : Bool) (sc : List DeclInfo) (ns : List String) (t : Term) : M DeclInfo := do
  let sub (u : Term) : M Unit := if chk then discard (declOf chk sc ns u) else pure ()
  match t with
  | .place p => placeDecl sc p
  | .borrow p => pure (.ref (← placeDecl sc p))
  | .zero | .tt => pure .other
  | .assign _ u | .succ u | .fst u | .snd u => sub u; pure .other
  | .letIn h u w => do
    let d ← declOf chk sc ns u
    declOf chk (d :: sc) (h.name :: ns) w
  | .seq u w => sub u; declOf chk sc ns w
  | .matchNat _ z s => pure (agreeDecl (← get).cfg.armsAgree [← declOf chk sc ns z, ← declOf chk sc ns s])
  | .matchInd _ _ arms => pure (agreeDecl (← get).cfg.armsAgree (← arms.mapM fun (_, a) => declOf chk sc ns a))
  | .const n =>     -- an unknown name is the machine's error, reported where it is met
    if let some d := (← get).constDecls.lookup n then return d
    tryCatch (do
        let d ← valTypeDecl (← lookupGlobal n).ty
        modify fun s => { s with constDecls := (n, d) :: s.constDecls }
        pure d) fun _ => pure .any
  | .val v => valueDecl v
  | .sort l => pure (.sort (l + 1))
  | .nat | .unit => pure (.sort 1)
  | .ref A => discard (typePos chk sc ns A); pure (.sort 1)
  | .pi hs ds c => do
    let (sc', ns', l) ← telescope chk sc ns hs ds
    let lc ← typePos chk sc' ns' c
    pure (.sort (if lc == 0 then 0 else max l lc))
  | .fix self hs ds c _ body => do
    let (sc', ns', _) ← telescope chk sc ns hs ds
    discard (typePos chk sc' ns' c)
    let cd ← typeDecl chk sc' ns' c
    if chk then
      -- the body sees the parameters, then `self`, then the enclosing scope
      let k := ds.length
      discard (declOf chk (sc'.take k ++ (DeclInfo.pi cd :: sc)) (ns'.take k ++ (self.name :: ns)) body)
    pure (.pi cd)
  | .call f as _ => do
    let df ← declOf chk sc ns f
    for a in as do sub a
    pure (match df with
      | .pi r => r
      | .prop => .prop      -- a proof applied is a proof (its type is a Π into a proposition)
      | .any => .any
      | _ => .other)
  | .eq A a b | .id A a b => do
    discard (typePos chk sc ns A); sub a; sub b; pure (.sort 0)
  | .cong f h => sub f; sub h; pure .prop
  | .ascribe u A => do discard (typePos chk sc ns A); sub u; typeDecl chk sc ns A
  | .prim "J" [A, a, b, P, h, u] => do
    discard (typePos chk sc ns A)
    for x in [a, b, h, u] do sub x
    -- `J(…) : P(b)`, a proposition when `P` returns propositions
    match ← declOf chk sc ns P with
    | .pi (.sort 0) => pure .prop
    | _ => pure .other
  | .prim "trans" as | .prim "symm" as | .prim "rewrite" as | .prim "rewriteR" as =>
    for a in as do sub a
    pure .prop   -- D60: `rewrite h in u` is `J`, a proof
  | .prim "split" [_, u] | .prim "splitArms" [_, u] => declOf chk sc ns u   -- D61: its body's
  | .prim "clone" [u] => declOf chk sc ns u
  | .prim _ as => for a in as do sub a
                  pure .other
  | .tind n as => do
    for a in as do discard (typePos chk sc ns a)
    tryCatch (do pure (.sort (← lookupInd n).sort)) fun _ => pure (.sort 1)
  | .ctor ty _ _ ps as => do
    for p in ps do discard (typePos chk sc ns p)
    for a in as do sub a
    pure (if ← tryCatch (ctorIsProof ty) (fun _ => pure false) then .prop else .other)

/-- What a type term says as a declared type: a sort, a Π-type, a borrow type, or a
proposition when its own declared type is `Prop`. -/
partial def typeDecl (chk : Bool) (sc : List DeclInfo) (ns : List String) (T : Term) : M DeclInfo := do
  match T with
  | .sort l => pure (.sort l)
  | .pi hs ds c => do
    let (sc', ns', _) ← telescope false sc ns hs ds
    pure (.pi (← typeDecl false sc' ns' c))
  | .ref A => pure (.ref (← typeDecl false sc ns A))
  | .val v => valTypeDecl v
  | _ => match ← declOf false sc ns T with
    | .sort 0 => pure .prop
    | .any => pure .any
    | _ => pure .other

/-- A term written where a type is expected: with `chk`, its declared type must be a sort
(D55). Returns the sort (`1` when not known). -/
partial def typePos (chk : Bool) (sc : List DeclInfo) (ns : List String) (T : Term) : M Nat := do
  if !chk then return 1
  match ← declOf chk sc ns T with
  | .sort l => pure l
  | .any => pure 1
  | .conflict => err (conflictMsg T ns)
  | _ =>
    if (← get).cfg.sortsSyntactic then
      err s!"[D55] {T.pp ns} is written where a type is expected, but its declared type is not a sort (it is a type only by computation)"
    else pure 1

/-- A telescope of binder types, each in the scope of the earlier ones: the extended
scope, and the largest of their sorts. -/
partial def telescope (chk : Bool) (sc : List DeclInfo) (ns : List String) (hs : List Hint)
    (ds : List Term) : M (List DeclInfo × List String × Nat) := do
  let mut sc := sc
  let mut ns := ns
  let mut l := 0
  for (h, d) in hs.zip ds do
    l := max l (← typePos chk sc ns d)
    sc := (← typeDecl chk sc ns d) :: sc
    ns := h.name :: ns
  pure (sc, ns, l)

/-- What a runtime value's declared type says (an embedded value, a capture). -/
partial def valueDecl (v : Value) : M DeclInfo := withLive false do
  match v with
  | .proof => pure .prop
  | .sort l => pure (.sort (l + 1))
  | .tNat | .tUnit | .tRef _ | .tInd .. | .tEq .. | .tPi .. =>
    pure (.sort (← tryCatch (sortOf v) (fun _ => pure 1)))
  | .gfn n => tryCatch (do valTypeDecl (← lookupGlobal n).ty) fun _ => pure .other
  | .clo cs (.fix _ hs ds c _ _) => do
    let capSc ← cs.reverse.mapM valueDecl
    let (sc', ns', _) ← telescope false capSc [] hs ds
    pure (.pi (← typeDecl false sc' ns' c))
  | .abs σ => tryCatch (do valTypeDecl (← absType σ)) fun _ => pure .other
  | .sealed t => declOf false [] [] t
  | .borrow _ _ => pure (.ref .other)
  | _ => pure .other

/-- What a type value says as a declared type (a stored or global type). -/
partial def valTypeDecl (T : Value) : M DeclInfo := withLive false do
  match T with
  | .sort l => pure (.sort l)
  | .tPi cs (.pi hs ds c) => do
    let capSc ← cs.reverse.mapM valueDecl
    let (sc', ns', _) ← telescope false capSc [] hs ds
    pure (.pi (← typeDecl false sc' ns' c))
  | .tRef A => pure (.ref (← valTypeDecl A))
  | _ => pure (if ← tryCatch (isPropV T) (fun _ => pure false) then .prop else .other)

/-- What each parameter's declared type says, each in the scope of the captured values
and the earlier parameters, and what the codomain says. -/
partial def paramDecls (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    M (List DeclInfo × DeclInfo) := do
  let capSc ← cs.reverse.mapM valueDecl
  let (sc', ns', _) ← telescope false capSc [] hs ds
  pure ((sc'.take ds.length).reverse, ← typeDecl false sc' ns' c)

/-- A binding's declared reading, completed for a function: a declared type that is a
Π-type only after computing it (`p : Pow(Nat)`) says what the Π-type value says, and a
function value has the class of its own declared Π-type (D54 makes the two agree). -/
partial def refineDecl (d : DeclInfo) (A? : Option Value) (v : Value) : M DeclInfo := do
  if d != .other then return d
  if let some A@(.tPi ..) := A? then return ← valTypeDecl A
  match v with
  | .gfn _ | .clo _ _ => valueDecl v
  | .abs σ => match ← tryCatch (absType σ) (fun _ => pure .bot) with
    | .tPi .. => valueDecl v
    | _ => pure d
  | _ => pure d

/-- Push captured values as bindings, each with what its declared type says. -/
partial def pushCaps (cs : List Value) : M Unit := do
  for v in cs do
    let d ← valueDecl v
    modifyFrame (← topIdx) fun fr =>
      { fr with binds := fr.binds.push { hint := ⟨"κ"⟩, ty := none, val := v, decl := d, cap := true } }

/-- Push parameters with their declared-type readings (the earlier ones in scope). -/
partial def paramDecl (d : Term) : M DeclInfo := withLive true (typeDecl false [] [] d)

/-- The erasure pre-pass: whether a term is erased and whether it is a proof, decided
before it runs, from declared types. A proof is a term whose declared type is a
proposition; a call returning types is erased too (its context is not: D35). -/
partial def preFlags (t : Term) (d : DeclInfo) : M (Option (Bool × Bool)) := do
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
  | .tRef T => pure (.borrow (← freshLoan) (← absOf T))
  | _ => absOf A

/-- A fresh abstract value of type `T`, in η-normal form: at `Unit`, `()` (D59 refined: the
readback at type `Unit` is `()`; a value of `Unit` carries nothing). -/
partial def absOf (T : Value) : M Value := do
  if (← get).cfg.unitEta && T == .tUnit then return .unit
  pure (.abs (← freshAbs T))

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
  let mut through : List Nat := []   -- stuck-block borrow parameters, captured by their content
  let top0 := (← get).env.back!
  for o in fvs do
    -- [Fix] captures no borrow, a stuck block's borrow parameter included (D63, rule-audit
    -- item 7). The earlier device (fuzz-port R2 (ii), switch `blockRefCapture`) captured the
    -- content behind the parameter instead, which no printed rule does.
    let b0 := top0.binds[top0.binds.size - 1 - o]!
    let viaRef := (← get).cfg.blockRefCapture && b0.blockRef &&
      (t.freeOccs.filter (·.1 == o)).all fun (_, q, _) => q.derefsRoot
    if viaRef then through := o :: through
    let p := if viaRef then Place.deref (.var o) else Place.var o
    accessPath p; accessInside p
    let v ← content p
    match v with
    | .borrow _ _ =>
      let n := ((← get).env.back!.binds[(← get).env.back!.binds.size - 1 - o]!).hint.name
      err s!"a closure or Π-type captures the borrow {n} (closures capture no borrows, RULES §1)"
    | .bot => err "a closure or Π-type captures a moved place"
    | .ghost w =>
      -- D53: an erased closure or Π-type reads a moved value's ghost
      if (← get).erasedDepth > 0 && (← get).cfg.ghosts then vals := vals.push w.unghost
      else err "a closure or Π-type captures a moved place"
    | _ =>
      -- D64 [Repack]: a closure or Π-type captures the value whole
      if (← get).typing then
        if let some T := b0.ty then
          unless viaRef do repackCheck s!"a closure or Π-type captures {b0.hint.name}" v T
      if (← get).erasedDepth > 0 then vals := vals.push v.unghost
      else
        vals := vals.push v
        -- D53: a runtime closure moves the variables it captures whose types are not copies
        if !(v matches .proof) then
          if v.hasHole then err "[D53] a closure captures a place that was partly moved out"
          unless ← copyRead p v do
            if (← get).cfg.fnRule && (← isCapture p) then
              err s!"[D53] a closure's body moves a captured value ({← ppPlace p}) into a closure; clone it"
            logEffect p "moves"
            setPlace p (if (← get).cfg.ghosts then .ghost v else .bot)
  let idx (o : Nat) : Nat := (fvs.findIdx? (· == o)).getD 0
  let t0 := if through.isEmpty then t else
    t.mapFreePlace (fun c q => (if through.contains q.root then q.stripDeref else q).mapRoot fun j => .var (j + c)) 0
  let mut t' := t0.mapFree (fun c o => .var (c + m - 1 - idx o)) 0
  -- a captured proof keeps its type: its reads are inlined as `(⋆ : T)` (a proof's value
  -- is ⋆, so the type is all there is to record). "A proof" is the binding's declared
  -- flag, never its value (finding P3: `g(0)` may be ⋆ at an instance only)
  if (← get).cfg.capTypes then
    let top := (← get).env.back!
    for (o, k) in fvs.zipIdx do
      let b := top.binds[top.binds.size - 1 - o]!
      if b.proof && !through.contains o then
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
  -- D54: the erasure class, and whether it returns a borrow, are part of the Π-type (the
  -- `Unit` and data rows of [Close] may differ: `Unit` has one value, D54 refined)
  if (← get).cfg.classInType then
    unless (← fnClass P) == (← fnClass Q) && ((← declKind P) == .ref) == ((← declKind Q) == .ref) do
      return false
  if (← get).convStack.contains (P, Q) then return false
  tryCatch (onCopy do
      modify fun s => { s with env := #[{}], convStack := (P, Q) :: s.convStack }
      pushFrame
      pushCaps cs
      let (pds, _) ← paramDecls cs hs ds c
      let mut ws : Array (Value × Value) := #[]
      for ((d, h), pd) in (ds.zip hs).zip pds do
        let A ← evalType d
        let w ← match A with
          | .tRef T =>
            let c ← absOf T
            let l ← freshLoan
            modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
            pure (Value.borrow l c)
          | _ => genericValue A
        let pd' ← refineDecl pd (some A) w
        pushBind h (some A) w pd'.isProof pd'
        ws := ws.push (w, A)
      let C ← evalType c
      discard popFrameRaw
      pushFrame
      pushCaps cs'
      let (pds', _) ← paramDecls cs' hs ds' c'
      for (((d', h), (w, A)), pd) in ((ds'.zip hs).zip ws.toList).zip pds' do
        let A' ← evalType d'
        unless ← conv A A' do return false
        let pd' ← refineDecl pd (some A') w
        pushBind h (some A') w pd'.isProof pd'
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
  let .tPi cs (.pi hs ds c) := pf | return false
  -- a comparison that errors (e.g. a stuck block's function run at a generic argument where
  -- a pattern's sub-place does not exist, fuzz-port R3) answers "not convertible", as `convPi`
  tryCatch (convFnRun f g pf cs hs ds c) fun _ => pure false

/-- `convFn`'s observation of both functions' generic calls. -/
partial def convFnRun (f g pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    M Bool := do
  let mode := (← get).cfg.closureConv
  onCopy do
    modify fun s => { s with env := #[{}], convStack := (f, g) :: s.convStack }
    pushFrame
    pushCaps cs
    let (pds, _) ← paramDecls cs hs ds c
    let mut args := #[]
    for ((d, h), pd) in (ds.zip hs).zip pds do
      let A ← evalType d
      let w ← match A with
        | .tRef T =>
          let c ← absOf T
          let l ← freshLoan
          modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
          pure (Value.borrow l c)
        | _ => if ← isPropV A then pure Value.proof else absOf A
      let pd' ← refineDecl pd (some A) w
      pushBind h (some A) w pd'.isProof pd'
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
      wholeReturned r
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
    -- D53: functions are compared as code, with their moves (fuzz-port shape (c)), wherever
    -- the comparison is asked (a statement's is erased)
    let (rf, cf) ← withRuntime (obs f)
    let (rg, cg) ← withRuntime (obs g)
    let sameRes ← conv rf rg
    if mode == 2 then pure sameRes      -- counterfactual: compare the result only (breaker-fresh F3)
    else pure (sameRes && (← convList cf cg))

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
        let dd ← lookupInd t
        -- D64 (D52 restricted): a dependent constructor is taken apart only while its index
        -- fields are convertible on both sides, so that each field equation is at one type
        -- (the field types computed from either side's earlier fields agree). Otherwise the
        -- equation stays: fail-safe, incomplete (OTT's rule needs a dependent conjunction)
        let blocked ← if dd.dependent c && cfg.depInj then
            (dd.indexFields c).anyM fun j => do pure !(← conv (fs.getD j .bot) (gs.getD j .bot))
          else pure false
        if blocked then fire .EqStuck fun _ => s!"{a} and {b}: index fields not convertible (D64)"
        if !blocked then
          if dd.dependent c then fire .EqInj fun _ => s!"{a} and {b}: index fields convertible (D64)"
          let Ts ← fieldTypesOf dd args c fs
          if Ts.length == fs.length then
            let eqs ← ((Ts.map (·.2)).zip (fs.zip gs)).mapM fun (T, (v, w)) => mkEqM T v w
            return andList eqs
  | _, _ => pure ()
  if cfg.disjoint && distinctCtors a b then pure vFalse
  else pure (.tEq A a b)

-- ### Evaluation

/-- D60 [Rewrite]: the goal `G` of `rewrite h in t` after the rewrite, i.e. the type `t`
must have. With `h : Eq A a b`, every occurrence of `b`'s normal form in `G` is generalised
to a fresh `σ` (the replacement [Split] uses to generalise a sealed program, D34, here local
to the goal and not recorded), and `a` is substituted for `σ`, re-normalising what changed.
`rev` (`rewrite ← h in t`) swaps `a` and `b`. The term is `J(A, a, b, λz. G[z/b], h, t)`
with the motive read off the goal. A rewrite that finds nothing to rewrite is an error (a
wrong direction, usually); an `h` whose type computes to `True` rewrites nothing and is
allowed (its two sides are already equal). -/
partial def rewriteGoal (rev : Bool) (h : Term) (G : Value) : M Value := do
  unless (← typeClass G) == 2 do err s!"rewrite: the goal {G} is not a proposition"
  let (_, Th) ← eval true h
  match Th.map unitTop with
  | some (.tInd "True" []) => pure G
  | some (.tEq A a b) =>
    let (src, dst) := if rev then (a, b) else (b, a)
    let σ ← freshAbs A
    let G1 ← substV src (.abs σ) G
    -- [T-Rewrite] has no premise that `b` occurs: a rewrite that finds nothing leaves the goal
    -- as it is (G' = G), and `t` is checked against it (rule-audit C22)
    let G' ← substV (.abs σ) dst G1
    trace fun _ => s!"[Rewrite] {src} ↦ {dst}: goal {G'}"
    pure G'
  | some T => err s!"rewrite: the proof has type {T}, which is not an equation"
  | none => err "rewrite: untyped proof"

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
  -- the erasure pre-pass: decided before the term runs, from declared types (a call's
  -- head is not classified: its flags are the call's)
  let head := (← get).headEval
  let hinted := (← get).tailDecl     -- a sequencing form hands its reading to its tail
  modify fun s => { s with headEval := false, tailDecl := none }
  let d? ← if (← get).cfg.prePass && !head && !(t matches .val _) then
      match hinted with
      | some d => pure (some d)
      | none => some <$> withLive true (declOf false [] [] t)
    else pure none
  modify fun s => { s with curDecl := d? }
  let pre ← match d? with
    | some d => preFlags t d
    | none => pure none
  -- D53: an erased term's reads copy, decided before it runs
  -- (tracked with or without D53: K2/K3 read it too)
  let typing0 := (← get).typing
  modify fun s => { s with typing := typed }
  let r ← tryCatch (withErasedIf (pre matches some (true, _)) (evalCore typed t hint))
    fun e => do modify (fun s => { s with typing := typing0 }); throw e
  modify fun s => { s with typing := typing0 }
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
        let (_, p) ← getFlags
        pure (p, p)
      | .cong _ _ | .prim "trans" _ | .prim "symm" _ => pure (true, true)
      | .prim "rewrite" _ | .prim "rewriteR" _ => pure (true, true)   -- D60: `J`, a proof
      | .ctor ty _ _ _ _ => let p ← ctorIsProof ty; pure (p, p)   -- D42: a Prop inductive's value is a proof
      | .prim "J" [_, _, _, P, _, _] =>
        let p ← jErased P      -- the appendix's clause 4: the motive is syntactically into Prop
        pure (p, p)
      | .ascribe (.val .proof) _ => pure (true, true)
      | .ascribe _ A =>
        -- a proof if the ascribed term is, or if the annotation's declared sort is Prop
        let p := (← getFlags).2 || (← withLive true (typeDecl false [] [] A)).isProof
        pure (p, p)
      | .place _ | .const _ | .val _ | .fix .. =>
        let p ← match cfg.leafRule with
          | 0 => pure false
          | 1 => pure (r.1 == .proof)     -- finding P1's first fix: unstable (finding P3)
          | _ => leafProof t r.1
        pure (p, p)
      | _ => pure (false, false)
    else do let e ← erasedValue r.1; pure (e, e)   -- the v1.4 reading: decided on the value (breaker-fresh F1)
  -- the after-the-fact classification is kept as an assertion that the two agree (under
  -- the rules as they stand; a counterfactual switch changes the after-the-fact one)
  let (erased, proof) ← match pre with
    | some f =>
      let pa ← match (← get).preAssert with
        | some b => pure b
        | none => do
          let b := cfg.prePassAssert
          modify fun s => { s with preAssert := some b }
          pure b
      if pa && f != (erased, proof) then
        err s!"INTERNAL [pre-pass] {t.pp []}: erased/proof = {f} by its declared type, {(erased, proof)} after running (please report)"
      pure f
    | none => pure (erased, proof)
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
sort is `Prop` (`typeDecl`, D63), never by evaluating it (formal-appendix BoomL). The
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
      | .val _ => pure 0     -- a stuck block's function (`closeOffMatch`): its class is given at its call
      | _ =>
        -- read from the codomain term, never evaluated (D35), by the one reader of declared
        -- types (`typeDecl`, D63): proofs if the codomain's declared sort is `Prop`
        let capSc ← cs.reverse.mapM valueDecl
        let (sc', ns', _) ← telescope false capSc [] hs ds
        pure (if (← typeDecl false sc' ns' c).isProof then 2 else 0)
    | _ => pure 0
  modify fun s => { s with classCache := (piTy, k) :: s.classCache }
  pure k

/-- v1.7 (D35): which parameters are proofs, i.e. declared of sort Prop, read by the one
reader of declared types (`typeDecl` over the telescope, in the scope of the captured values and
the earlier parameters, D63). The same flags wherever parameters are bound: the body, [Def]
and [Call-type]. -/
partial def paramFlags (cs : List Value) (ds : List Term) : M (List Bool) := do
  if (← get).cfg.leafRule != 2 then return ds.map fun _ => false
  let quick : Term → Bool := fun
    | .nat | .unit | .ref _ | .sort _ | .tind "Pair" _ => true
    | _ => false
  if ds.all quick then return ds.map fun _ => false
  let capSc ← cs.reverse.mapM valueDecl
  let (sc', _, _) ← telescope false capSc [] (ds.map fun _ => ⟨"_"⟩) ds
  pure ((sc'.take ds.length).reverse.map (·.isProof))

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
  | .const n => pure (← valTypeDecl (← lookupGlobal n).ty).isProof
  | .fix .. => match v with
    | .proof => pure true
    | .clo cs (.fix _ hs ds c _ _) => pure ((← fnClass (.tPi cs (.pi hs ds c))) == 2)
    | _ => pure false
  | _ => pure false

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
  pure ((← withLive true (declOf false [] [] P)) matches .pi (.sort 0))

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
    if let some T := T then repackAt p T "read whole"
    pure (← readPlace p, T)
  | .borrow p =>
    let T ← if typed then some <$> placeType p else pure none
    if let some T := T then
      if T.typeHasRef then err s!"&{← ppPlace p}: a borrow of a borrow-typed place"
      -- D48 (1) for terms ([T-Borrow]'s premise, reviewer-6's A12): the borrowed place's
      -- type is data, as for the type former `&A`
      if (← get).cfg.refData && !(← isDataType T) then
        err s!"[D48] &{← ppPlace p}: its type {T} is not a data type (Nat, Unit, ×, an inductive type in Type); only data is borrowed"
      repackAt p T "borrowed whole"
    let b ← borrowPlace p
    openWrite p
    pure (b, T.map .tRef)
  | .assign p u =>
    -- the place's type is the type the context requires of a constructor's parameters and of an
    -- embedded value with no type of its own (an inert loan in a sealed program's `*r := loan`)
    let hint ← if typed && (u matches .ctor .. | .val _) then
        tryCatch (some <$> placeType p) fun _ => pure none
      else pure none
    let (v, Tv) ← eval typed u hint
    -- D64 [Open]: a field whose declared type mentions earlier fields takes any value (a strong
    -- update: while its value is open it is typed by what it holds); [Repack] checks it later
    -- [Open]: a strong update
    if typed && (← strongUpdate p) then fire .Open fun _ => s!"a strong update of a dependent field, to a value of type {Tv.getD .bot}"
    if typed && !(← strongUpdate p) then expectTy "the assigned value" Tv (← placeType p)
    assignPlace p v
    openWrite p
    pure (.unit, ty .tUnit)
  | .letIn h u w =>
    let myD := (← get).curDecl
    let du ← if (← get).cfg.prePass then withLive true (declOf false [] [] u) else pure .other
    let (v, T) ← eval typed u
    let du' ← refineDecl du T v
    -- `h` is a proof iff `u` is, or its declared type is a proposition (P1; `u` may be an
    -- embedded value, `⋆` in a sealed program's bindings, which the pre-pass does not read)
    let p := (← getFlags).2 || ((← get).cfg.leafRule == 2 && du'.isProof)
    pushBind h T v p du'
    -- the tail's reading is this let's (read with `h`'s declared type, unless refined)
    if du' == du then modify fun s => { s with tailDecl := myD }
    let (r, R) ← eval typed w
    let fl ← getFlags     -- the body's erasure flags (dropping may normalise)
    pushTemp r
    dropTopBind
    setFlags fl
    pure (← popTemp, R)
  | .seq u w =>
    let myD := (← get).curDecl
    let (v, _) ← eval typed u
    dropValue v
    modify fun s => { s with tailDecl := myD }     -- the tail's reading is this sequence's
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
    if !typed then return (v, none)
    -- an embedded value with no type of its own (a proof, an inert loan) has the type of the
    -- position it was embedded at: a parameter's or a field's declared type (the hint)
    match v, hint with
    | .proof, some T => if ← isPropV T then pure (v, some T) else pure (v, some (← valType v))
    | .loan _, some T => tryCatch (do pure (v, some (← valType v))) fun _ => pure (v, some T)
    | _, _ => pure (v, some (← valType v))
  | .sort l => pure (.sort l, some (.sort (l + 1)))
  | .pi _ ds c =>
    borrowParamCheck ds c
    -- a type former is erased: even its captures (which access places) run on a copy
    let (cs, t') ← onCopy (withErased (capture t))
    let T := Value.tPi cs t'
    if typed then pure (T, some (.sort (← sortOf T))) else pure (T, none)
  | .fix _ hs ds c _ _ =>
    borrowParamCheck ds c
    -- a closure whose calls are erased is itself erased by the pre-pass (its captures copy)
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
  | .eq A a b => onCopy <| withErased do
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
  | .id A a b => pure (← withErased (idType typed A a b), some (.sort 0))
  | .prim "J" [A, a, b, P, h, u] =>
    -- J(A, a, b, P, h, t) : P(b) for h : Eq A a b and t : P(a) (endpoints explicit, D23)
    if !typed then
      if (← get).cfg.jStuck && !(← jErased P) then
        -- its endpoints are erased positions, on private copies, confined; `A`, `P` and `h`
        -- are never run by the machine (A.191)
        let (av, _) ← confinedCopy "J's endpoint" (eval false a)
        let (bv, _) ← confinedCopy "J's endpoint" (eval false b)
        -- [J]: the endpoints are convertible, `J` is `t`; [J-stuck]: otherwise the run is
        -- stuck, and `t` does not run (D56, D63, rule-audit item 5)
        if ← conv av bv then return ← eval false u
        stuckNow
      return (← eval false u)
    let A' ← evalType A
    let (av, Ta) ← confinedCopy "J's endpoint" (eval true a)
    let (bv, Tb) ← confinedCopy "J's endpoint" (eval true b)
    expectTy "J's first endpoint" Ta A'
    expectTy "J's second endpoint" Tb A'
    let (Pv, PT) ← confinedCopy "J's motive" (eval true P)
    let (_, Th) ← eval true h
    let hT ← mkEqM A' av bv
    expectTy "J's equation" Th hT
    let (Pa, _) ← callFn true Pv PT #[av] #[some A'] false
    let (Pb, _) ← callFn true Pv PT #[bv] #[some A'] false
    if (← get).cfg.jStuck && !(← jErased P) && !(← conv av bv) then
      -- [T-J-stuck]: the machine would be stuck, so typing checks `t` against `P(a)` on a
      -- private copy and closes the `J` off as a stuck block of type `P(b)`, as [Split] closes
      -- off a stuck match; its sealed programs run `t` once a refinement makes the endpoints
      -- convertible (D63, rule-audit item 5)
      let saved ← get
      let f0 := (← get).env.size - 1
      let n0 := (← get).env[f0]!.binds.size
      let ls := (← get).placeLog.size
      let (_, Tu) ← eval true u (some Pa)
      expectTy "the transported term" Tu Pa
      let moved ← armMoves ((← get).placeLog.extract ls (← get).placeLog.size) f0 n0
      restoreKeep saved
      -- the endpoints, motive and equation are erased positions, formed once here: the block
      -- embeds their values and captures only `t`'s places
      let tJ := Term.prim "J" [.val A', .val av, .val bv, .val Pv, .ascribe (.val .proof) (.val hT), u]
      return ← closeOffMatch tJ Pb moved false
    let (v, Tu) ← eval true u
    let fl ← getFlags
    expectTy "the transported term" Tu Pa
    setFlags fl    -- t's flags (J is t)
    pure (v, some Pb)
  | .prim "symm" [h] =>
    let (_, Th) ← eval typed h
    match Th.map unitTop with
    | some (.tEq A a b) => pure (.proof, some (← mkEqM A b a))
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    -- an equation that computes to `False` (a refinement made it impossible) is symmetric
    -- to one that does too (fuzz-port R7)
    | some (.tInd "False" []) => pure (.proof, some (.tInd "False" []))
    | _ => if typed then err "symm: not an equation" else pure (.proof, none)
  | .prim "trans" [h, k] =>
    let (_, Th) ← eval typed h
    let (_, Tk) ← eval typed k
    if !typed then return (.proof, none)
    match Th.map unitTop, Tk.map unitTop with
    | some (.tInd "True" []), some T | some T, some (.tInd "True" []) => pure (.proof, some T)
    | some (.tInd "False" []), _ | _, some (.tInd "False" []) => pure (.proof, some (.tInd "False" []))
    | some (.tEq A a b), some (.tEq A' b' c) =>
      unless (← conv A A') && (← conv b b') do err s!"trans: {Th.get!} and {Tk.get!} do not compose"
      pure (.proof, some (← mkEqM A a c))
    | _, _ => err "trans: not equations"
  | .prim "rewrite" [h, u] | .prim "rewriteR" [h, u] =>
    -- D60 [Rewrite]: checked against the type the context requires (`hint`)
    if !typed then return (.proof, none)
    let some G := hint
      | err "rewrite: the goal is not known here (use it in tail position, as a call's argument, or under an annotation `let x : T = …`)"
    let G' ← rewriteGoal (t matches .prim "rewriteR" _) h G
    let (_, Tu) ← eval true u (some G')
    expectTy "the rewritten term" Tu G'
    pure (.proof, some G)
  | .prim "split" _ | .prim "splitArms" _ => err "split: only in tail position (where the goal is known)"
  -- D53: `clone(p)` copies `p` (an erased read); `peek` is an observation's final read
  | .prim "clone" [u] =>
    -- K2: cloning a view at runtime copies it
    if let .place p := u then
      if let some v ← tryCatch (some <$> content p) (fun _ => pure none) then unsizedCheck p v "cloned"
    withErased (eval typed u hint)
  | .prim "peek" [u] => withErased (eval typed u hint)
  | .prim "inplace" [t] =>
    if t matches .place _ then modify fun s => { s with inPlace := true }
    let r ← eval typed t hint
    modify fun s => { s with inPlace := false }
    pure r
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
      let pd' ← withLive true (typeDecl false [] [] PT)
      pushBind h (some A) v pd'.isProof pd'

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
  if d.abstract && (← get).cfg.abstractTypes && (← atRuntime) then
    err s!"[K3] the constructor {h.name} of the abstract type {ty} at runtime, outside model code (an `implemented by` body, or a function taking or returning an unsized value)"
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
  let mut ws0 : Array Value := #[]
  -- D64: a dependent field's hint is its type at the fields evaluated so far
  let dep := d.dependent c
  for ((a, (_, FT)), i) in (as.zip fields).zipIdx do
    let fh ← if typed && ((np > 0 && (a matches .ctor .. | .prim "rewrite" _ | .prim "rewriteR" _)) || (a matches .val _)
        || (dep && d.fieldDependent c i))
      then fieldTypeAt d sol c i ws0.toList else pure none
    let (w, T) ← eval typed a fh
    if let some T := T then sol := unifyParams np FT T sol
    tys := tys.push T
    pushTemp w
    ws0 := ws0.push w
  let ws ← popTemps as.length
  let proof ← ctorIsProof ty
  if !typed then
    return (if proof then .proof else .ind ty c h evs.toList ws.toList, none)
  let mut ps := #[]
  for (s, (ph, _)) in sol.toList.zip d.params do
    match s with
    | some p => noBorrowParam ty p; ps := ps.push p
    | none => err s!"cannot infer the parameter {ph.name} of {h.name}: write it, {h.name}[…](…), or annotate, ({h.name}(…) : {ty}(…))"
  -- [T-Ctor], D64: each field against its type computed from the earlier fields' values
  for (T, (fname, FT)) in tys.toList.zip (← fieldTypesOf d ps.toList c ws.toList) do
    expectTy s!"field {fname} of {h.name}" T FT
  let v := if proof then Value.proof else .ind ty c h ps.toList ws.toList
  pure (v, some (mkTInd ty ps.toList (← get).cfg.unitNorm))

-- ### Calls: [Call], P5, [Call-type], [Close], [Rec]

partial def evalCall (typed : Bool) (f : Term) (as : List Term) (head : Bool)
    (cls? : Option Nat := none) : M (Value × Option Value) := do
  modify fun s => { s with headEval := true }
  -- D53 (e): a call does not consume the function it calls (read in place)
  if (← get).cfg.fnRule && (f matches .place _) then modify fun s => { s with inPlace := true }
  let (fv, fT) ← eval typed f
  modify fun s => { s with inPlace := false }
  pushTemp fv
  let mut tys := #[]
  let mut argSteps : Array (Nat × Nat) := #[]   -- D41: the borrows and moves that evaluate arguments
  let mut ws0 := #[]
  for a in as do
    let s := (← get).effects.size
    -- v2.0: a constructor argument's parameters may come from the parameter's type
    let hint ← if typed && (a matches .ctor .. | .val _ | .prim "rewrite" _ | .prim "rewriteR" _) then argHint fv fT ws0 else pure none
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
      let .tPi cs (.pi hs ds c) ← funType fv fT | return none
      let some d := ds[ws.size]? | return none
      onCopy do
        pushFrame
        pushCaps cs
        let (pds, _) ← paramDecls cs hs ds c
        for (((d', h), w), pd) in ((ds.zip hs).zip ws.toList).zip pds do
          let A ← evalType d'
          let pd' ← refineDecl pd (some A) w
          pushBind h (some A) w pd'.isProof pd'
        some <$> evalType d)
    fun _ => pure none

/-- The Π-type of a function value. -/
partial def funType (fv : Value) (fT : Option Value) : M Value := do
  if let some T := fT then return T
  match fv with
  | .gfn n => pure (← lookupGlobal n).ty
  | .clo cs (.fix _ hs ds c _ _) => pure (.tPi cs (.pi hs ds c))
  | .abs σ => absType σ
  | .sealed _ =>
    -- D56: a stuck cast can be a function; its type is its program's (`sealedType`)
    tryCatch (valType fv) fun _ =>
      err s!"the type of the sealed function {fv} is not known here (a call of a sealed function in untyped code)"
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
    pushCaps cs
    let (pds, _) ← paramDecls cs hs ds c
    for (((d, h), i), pd) in ((ds.zip hs).zipIdx).zip pds do
      let A ← evalType d
      expectTy s!"argument {i + 1} ({h.name})" tys[i]! A
      pushBind h (some A) ws[i]! (pf.getD i false) (← refineDecl pd (some A) ws[i]!) (d matches .val (.tRef _))
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
  let .fix self hs ds c _ body := t | err "internal: not a fix"
  -- K2/K3: a model function's body never runs at runtime
  let model ← match fv with
    | .gfn n => do pure (← lookupGlobal n).model
    | _ => pure false
  if model then modify fun s => { s with modelDepth := s.modelDepth + 1 }
  let r ← tryCatch (runBodyCore fv cs t ws self hs ds c body) fun e => do
    if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }
    throw e
  if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }
  pure r

partial def runBodyCore (fv : Value) (cs : List Value) (t : Term) (ws : Array Value) (self : Hint)
    (hs : List Hint) (ds : List Term) (c : Term) (body : Term) : M Value := do
  let d := (← get).depth
  if d ≥ 2000 then err "call depth exceeded (a non-terminating recursion)"
  modify fun s => { s with depth := d + 1 }
  let pf ← paramFlags cs ds
  let (pds, cd) ← paramDecls cs hs ds c
  -- a proof parameter that a function or Π-type in the body may capture needs its type,
  -- which is all a captured proof records (`capture`): read it off the declared domain,
  -- at the arguments (arrays-library: a Π whose body uses a proof captured from outside it)
  let ptys ← if body.formsFn && (pf.any id || pds.any (·.isProof)) then onCopy do
      pushFrame
      pushCaps cs
      let mut out := #[]
      for ((((h, w), p), pd), d) in (((hs.zip ws.toList).zip pf).zip pds).zip ds do
        let A? ← if p || pd.isProof then tryCatch (some <$> evalType d) (fun _ => pure none) else pure none
        out := out.push A?
        pushBind h A? w p pd
      pure out
    else pure #[]
  pushFrame
  pushCaps cs
  pushBind self none fv false (.pi cd)
  for (((((h, w), p), pd), d), i) in ((((hs.zip ws.toList).zip pf).zip pds).zip ds).zipIdx do
    pushBind h (ptys[i]?.getD none) w p (← refineDecl pd none w) (d matches .val (.tRef _))
  let es := (← get).effects.size
  -- D53: a body is code; a function whose calls are erased has an erased body (b)
  let erasedFn ← tryCatch (do pure ((← fnClass (← funType fv none)) != 0)) (fun _ => pure false)
  let (v, _) ← withErasedIf erasedFn (eval false body)
  wholeReturned v
  pushTempAt ((← topIdx) - 1) v
  popFrame
  -- the body's steps are rooted in its own frame, which is gone
  modify fun s => { s with depth := d, effects := s.effects.extract 0 es }
  popTemp

/-- D53 (fuzz-port shape (c)): a returned borrow's content must be whole, as when a borrow
ends: a function may not hand back a borrow of a place it moved out of. -/
partial def wholeReturned (v : Value) : M Unit := do
  if let .borrow _ c := v then
    if c.hasHole then
      err s!"[D53] a returned borrow's content is partly moved out ({c})"

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
  -- D54: the class and [Close] row are those of the function value's own declared Π-type,
  -- on every path (conversion only lets a value stand at a Π-type of its class and row, so
  -- this is also the static type's); without D54, the static type's where there is one
  let clsTy ← if (← get).cfg.classInType then tryCatch (funType fv none) (fun _ => pure piTy)
    else pure piTy
  -- [Close]'s row: v1.7 (D35) from the declared codomain; v1.6 from the computed type
  let byDecl := (← get).cfg.erasureByDecl
  let kind ← if byDecl then declKind clsTy else
    match B with
    | some B => kindOf B
    | none => resultKind piTy ws
  -- D28, D35: the callee's class, read off its declared codomain (a stuck block's is
  -- given by `closeOffMatch`)
  let cls ← match cls? with
    | some k => pure k
    | none => if byDecl then fnClass clsTy else pure (if kind == .prop then 2 else 0)
  let kind := if byDecl && kind == .prop then Kind.data else kind
  -- D53: an erased call cannot make whole a borrow it is passed (its effects vanish at runtime)
  if cls != 0 then wholeBorrowArgs ws "an erased call"
  if cls == 2 && (← get).cfg.p5 then
    endBorrowArgs ws
    setFlags (true, true)
    return (.proof, B)
  let r ← match fv with
    | .abs _ | .sealed _ =>
      -- a neutral head closes off at once (v1.3), except as [Seal]'s head call (D39)
      if head && (← get).cfg.headGuardNeutral then stuckNow else closeCall fv ws kind B
    | .gfn _ | .clo _ _ =>
      let (cs, t) ← fixOf fv
      tryCatch (runBody fv cs t ws) fun e =>
        match e with
        | .stuck fu _ =>
          if head then throw e
          else do
            modify fun s => { s with fuel := fu }
            closeCall fv ws kind B
        | .error m => throw (.error m)
    | _ => err s!"call of {fv}, which is not a function"
  let r := if cls == 2 then Value.proof else r
  setFlags (byDecl && cls != 0, byDecl && cls == 2)
  pure (r, B)

/-- D53 (fuzz-port P): a borrow passed at runtime to a call that closes off, or to an erased
call, must be whole. [Close] seals the borrowed place's content, which hides a hole, and an
erased call's writes vanish at runtime, so neither can make it whole before the borrow ends. -/
partial def wholeBorrowArgs (ws : Array Value) (what : String) : M Unit := do
  if (← get).erasedDepth > 0 then return
  for (w, i) in ws.toList.zipIdx do
    if let .borrow _ u := w then
      if u.hasHole then
        err s!"[D53] argument {i + 1} of {what} is a borrow whose content is partly moved out ({u})"

/-- D59 refined: a stuck call's result has type `Unit`: its declared codomain says so, or its
type as computed at the call (`B` in a typed run; otherwise computed here, when the declared
codomain does not say). -/
partial def resultIsUnit (fv : Value) (ws : Array Value) (kind : Kind) (B : Option Value) : M Bool := do
  if kind == .unit then return true
  if let some B := B then return B == .tUnit
  tryCatch (do
      let piTy ← funType fv none
      pure ((← resultKind piTy ws) == .unit)) fun _ => pure false

/-- [Close]: the call `f(w̄)` has a stuck body; the partial run has been discarded (the
state is back at the call point). `L := let cᵢ = uᵢ`, `C := f(ā)` with `aᵢ = &cᵢ` for
the borrow arguments `wᵢ = borrow_ℓᵢ uᵢ`; the result and the loans follow the table. -/
partial def closeCall (fv : Value) (ws : Array Value) (kind : Kind) (B : Option Value := none) : M Value := do
  wholeBorrowArgs ws "a call that closes off"
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
  let cfg := (← get).cfg
  let argT (d : Nat) (i : Nat) : Term :=
    match bs.findIdx? (·.1 == i) with
    | some j => .borrow (.var (d + m - 1 - j))
    | none => .val ws[i]!
  let C (d : Nat) : Term := .call (.val fv) ((List.range ws.size).map (argT d)) true
  let wrapL (body : Term) : Term :=
    (bs.zipIdx).foldr (fun ((_, _, u), j) acc => .letIn ⟨s!"c{j + 1}"⟩ (.val u) acc) body
  let cell (d j : Nat) : Term := .place (.var (d + m - 1 - j))
  -- D53: the final read of a sealed program (its `K`) is an observation: it copies, while
  -- the program before it runs with runtime semantics
  let peek (t : Term) : Term := .prim "peek" [t]
  match kind with
  | .ref =>
    let k ← freshLoan
    for ((_, l, _), j) in bs.zipIdx do
      let fill := wrapL (.letIn ⟨"r"⟩ (C 0) (.seq (.assign (.deref (.var 0)) (.val (.loan k))) (peek (cell 1 j))))
      substEnv (.loan l) (← canonNeutral (.sealed fill)) false
    pure (.borrow k (← canonNeutral (.sealed (wrapL (.letIn ⟨"r"⟩ (C 0) (peek (.place (.deref (.var 0)))))))))
  | _ =>
    for ((_, l, u), j) in bs.zipIdx do
      -- D59 refined: a borrowed place of type `Unit` (its content `()`) is filled with `()`
      let fill ← if cfg.unitEta && u == .unit then pure .unit
        else canonNeutral (.sealed (wrapL (.seq (C 0) (peek (cell 0 j)))))
      substEnv (.loan l) fill false
    -- D59 refined: the readback at type `Unit` is `()` (η-normal form); the call's effects
    -- are in the fills above. Without η, the row read off the declared codomain (v1.1–v2.0)
    if cfg.unitEta then
      if ← resultIsUnit fv ws kind B then return .unit
    else if kind == .unit then return .unit
    canonNeutral (.sealed (wrapL (C 0)))

/-- [Rec]: at a recursive call, a parameter position survives if its argument (the
content, through a borrow) is a strict subterm of that parameter's entry value as
refined so far. The recursive position is any position that survives every call.
Every enclosing function being checked is considered, so a recursive call inside a
nested closure is checked against the outer function's entry values (fix L3). -/
partial def recCheck (fv : Value) (ws : Array Value) : M Unit := do
  let st ← get
  if !st.cfg.recGuard then return
  let mut frames := #[]
  for ctx in st.recStack do
    if ctx.fn == fv then
      let cands := ctx.cands
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
      frames := frames.push { ctx with cands := cands' }
    else frames := frames.push ctx
  set { st with recStack := frames.toList }

-- ### Match: [Match], [Split], stuck blocks

/-- Apply a refinement `σ := r` to Ω, the stored types and the goal ([Split]). -/
partial def refine (σ : Nat) (r : Value) : M Unit := do
  substEnv (.abs σ) r true
  modify fun s => { s with refs := (σ, r) :: s.refs }
  if (← get).neutrals.any (·.2 == σ) then renormAll

partial def evalMatch (typed : Bool) (p : Place) (z s : Term) (expected : Option Value := none) :
    M (Value × Option Value) := do
  if typed then natScrutinee p
  accessPath p
  accessNeutralHead p
  let v ← matchContent p
  match v with
  | .zero => eval typed z
  | .succ _ => eval typed s
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ => if typed then splitThenClose p z s σ expected else stuckOn v
  | .sealed _ | .loan _ =>
    if !typed then stuckOn v
    else
      let σ ← generalizeNeutral p v
      let expected ← expected.mapM (substV v (.abs σ))
      splitThenClose p z s σ expected
  | _ => err s!"[Match] on a non-Nat value {v}"

/-- A match's constructors come from its scrutinee's type, never from its patterns: a match
on `Z`/`S` needs a scrutinee whose type normalises to `Nat` (fuzz-port's M2: `x : TG(σ)`,
stuck, was split as a `Nat`, and at `TG(1) = B2` the run met `F`). A type that is stuck is
not known to be `Nat` (fail-safe, as `scrutType` does for inductive matches). -/
partial def natScrutinee (p : Place) : M Unit := do
  if !(← get).cfg.scrutTyped then return
  match ← placeType p with
  | .tNat => pure ()
  | T => err s!"[Match] on {← ppPlace p} with `Z`/`S`, but its type {T} is not Nat"

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
  -- types re-normalise as types: erased, reads copy (D53)
  if let some g := (← get).goal then
    let g' ← withErased (renormV g)
    modify fun s => { s with goal := some g' }
  let f := (← get).env.size
  for fi in [0:f] do
    let n := (← get).env[fi]!.binds.size
    for i in [0:n] do
      if let some T := (← get).env[fi]!.binds[i]!.ty then
        let T' ← withErased (renormV T)
        modifyFrame fi fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }

partial def renormV (v : Value) : M Value := do
  if !(v.anyAtom fun | .sealed _ => true | _ => false) then return v
  match v with
  | .sealed t => do
    let t' ← renormT t
    canonNeutral (← nfSealed t')
  | .succ w => return .succ (← renormV w)
  | .ghost w => return .ghost (← renormV w)
  | .borrow l w => return .borrow l (← renormV w)
  | .ind ty c h ps fs => return .ind ty c h (← ps.mapM renormV) (← fs.mapM renormV)
  | .tEq A a b => mkEqM (← renormV A) (← renormV a) (← renormV b)
  | .tInd n as => return mkTInd n (← as.mapM renormV) (← get).cfg.unitNorm
  | .tRef A => return .tRef (← renormV A)
  -- closures and Π-types too: their captures and embedded values (arrays-library: a goal
  -- `… ∧ Π(…). …` whose Π captured a sealed program stayed stale after a split)
  | .clo cs t => return .clo (← cs.mapM renormV) (← renormT t)
  | .tPi cs t => return .tPi (← cs.mapM renormV) (← renormT t)
  | _ => return v

/-- Re-normalise the values embedded in a term (the sealed programs among them), everywhere
`substT` substitutes. -/
partial def renormT (t : Term) : M Term := do
  if !(t.anyAtom fun | .sealed _ => true | _ => false) then return t
  let go := renormT
  match t with
  | .val v => return .val (← renormV v)
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
  let saved ← get
  let mut tys : Array Value := #[]
  let mut moved : List Place := []
  let mut allProof := true
  let mut violation : Option String := none     -- D41: an arm with an outer effect
  let mut pending : Array Effect := #[]           -- D41: the arms' pending steps, judged after the block
  let f0 := (← get).env.size - 1
  let n0 := (← get).env[f0]!.binds.size
  for (mk, arm) in arms do
    let r ← mk
    refine σ r
    let ls := (← get).placeLog.size
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
    -- the arm's effect on the places it captures, read from its log of moves and
    -- assignments (D53: by place, at the granularity of the move, `q1.1`; an inner block's
    -- moves are its arguments', so they compose; fuzz-port M1, N1)
    let armMoved ← armMoves ((← get).placeLog.extract ls (← get).placeLog.size) f0 n0
    for q in armMoved do
      unless moved.any (placeEq · q) do moved := moved ++ [q]
    restoreArm saved
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

/-- D53: what a run left moved out among the bindings `(f0, i < n0)`, from its log of moves
and assignments in order: a move adds its place, an assignment restores every moved place it
covers. Places are rooted at the frame index the bindings had when the run started. -/
partial def armMoves (log : Array (Nat × Nat × Place × Bool)) (f0 n0 : Nat) : M (List Place) := do
  let mut out : List Place := []
  for (f, i, p, isMove) in log do
    if f != f0 || i ≥ n0 then continue
    let q := p.steps.2.foldl stepPlace (Place.var (n0 - 1 - i))
    if isMove then
      unless out.any (placeEq · q) do out := out ++ [q]
    else
      out := out.filter fun m => !placePrefix q m
  pure out

/-- The refinement of `σ` to constructor `c` of an inductive type at parameters `ps`:
fresh abstract values for its fields, of the fields' types; a field that is a proof
gets `⋆` (as a proof parameter does, D27). -/
partial def ctorRefinement (d : IndDecl) (ps : List Value) (c : Nat) : M Value := do
  let (cn, _) := d.ctors[c]!
  -- D64: each field's type from the earlier fields' fresh values (`σ₂ : T₂[σ₁]`)
  let fs := (← fieldsGeneric d ps c).map (·.2.2)
  pure (.ind d.name c ⟨cn⟩ ps fs)

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
  let v ← matchContent p
  if v == .bot then err s!"[Match] on {← ppPlace p}, which was moved out"
  if arms.isEmpty then
    if typed then
      let (d, _) ← scrutType p ty
      unless d.ctors.isEmpty do err s!"a match with no arms on {← ppPlace p} : {d.name}, which has constructors"
      if expected.isNone then err "annotate a match with no arms outside tail position (let x : T = match p {})"
    -- D58: reached, it is unreachable in a closed run. In a proof position it is erased
    -- (⋆); anywhere else it is stuck, closed off like a match on an abstract value, never
    -- a value of the wrong type
    if (← get).cfg.zeroArmStuck then
      if !typed then stuckNow
      let B := expected.get!
      unless ← isPropV B do return ← closeOffMatch (.matchInd p ty arms) B [] false
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
    restoreArm saved
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
    restoreArm saved
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
  abstractMatchCheck p ty
  if ← byTypeMatch ty arms then return ← evalMatchByType typed p ty arms expected
  accessPath p
  accessNeutralHead p
  let v ← matchContent p
  match v with
  | .ind t c _ _ _ =>
    if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
    if typed then discard (scrutType p ty)
    match arms[c]? with
    | some (_, a) => eval typed a
    | none => err s!"[Match] no arm for constructor {c}"
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ =>
    if !typed then stuckOn v
    else
      let (d, ps) ← scrutType p ty
      splitArmsThenClose (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement d ps c, a)) expected
  | .sealed _ | .loan _ =>
    if !typed then stuckOn v
    else
      let (d, ps) ← scrutType p ty
      let σ ← generalizeNeutral p v
      let expected ← expected.mapM (substV v (.abs σ))
      splitArmsThenClose (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement d ps c, a)) expected
  | _ => err s!"[Match] on {v}, which is not a value of {ty}"

/-- Two steps name the same part: a pair's `.1`/`.2` are its constructor's fields `fst`/`snd`
(the surface writes both; a Nat's `.1`, its predecessor, is never a pair's field). -/
partial def stepEq : Step → Step → Bool
  | .fst, .field g | .field g, .fst => g.ty == "Pair" && g.ctor == 0 && g.idx == 0
  | .snd, .field g | .field g, .snd => g.ty == "Pair" && g.ctor == 0 && g.idx == 1
  | a, b => a == b

/-- Place `q` is a prefix of place `p` (both rooted in the same frame). -/
partial def placePrefix (q p : Place) : Bool :=
  let (i, qs) := q.steps
  let (j, ps) := p.steps
  i == j && qs.length ≤ ps.length && ((ps.take qs.length).zip qs).all fun (a, b) => stepEq a b

/-- The same place (up to `stepEq`). -/
partial def placeEq (q p : Place) : Bool :=
  q.steps.2.length == p.steps.2.length && placePrefix q p

/-- D53: a place an arm moved out, as it exists in the closed-off (unrefined) state. The
arm's refinement may have exposed it (`q0.1` of an abstract pair, `n0`'s predecessor):
through a value of a single-constructor type the abstract value is refined to that
constructor, a total refinement (as a split with one arm); through any other, the move is
of the longest prefix that exists, since some arm moves a part of it (fuzz-port M1). -/
partial def movedPlace (q : Place) : M Place := do
  if ← tryCatch (do discard (content q); pure true) (fun _ => pure false) then return q
  let parent : Place → Option Place
    | .deref p | .fst p | .snd p | .field _ p => some p
    | .var _ => none
  let some p := parent q | return q
  let p ← movedPlace p
  match ← content p with
  | .abs σ =>
    match ← absType σ with
    | .tInd n ps =>
      let d ← lookupInd n
      if d.ctors.length == 1 then
        refine σ (← ctorRefinement d ps 0)
        movedPlace q
      else pure p
    | _ => pure p
  | _ => pure p

/-- Stuck blocks (RULES §3, v1.3): close a stuck match off as a call to an anonymous
function of its free places, captured as Rust infers closure captures, on maximal place
prefixes: a place some arm moves out of is moved in; otherwise a place written or
borrowed (under `&_` or left of `:=`) in some arm is passed as `&`; otherwise a place
read is copied. A borrow variable read as a whole is a move (reading a borrow moves it);
assigning a borrow variable as a whole moves it too (passing `&x` would be `&&T`). -/
partial def closeOffMatch (mt : Term) (B : Value) (moved : List Place) (allProof : Bool) :
    M (Value × Option Value) := do
  let moved ← moved.foldlM (fun acc q => do
      let q' ← movedPlace q
      pure (if acc.contains q' then acc else acc ++ [q'])) []
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
  -- the free places used, re-rooted at the frame index, with their capture mode
  -- (0 = copy, 1 = &, 2 = move)
  let scrut : Option Place := match mt with
    | .matchNat sp _ _ | .matchInd sp _ _ => some sp
    | _ => none
  let mut uses : Array (Place × Nat) := #[]
  let mut wholeUses : Array (Place × PKind) := #[]   -- D53: how each place is used as a whole
  for (o, p, k) in mt.freeOccsBlock do
    let q := p.mapRoot fun _ => .var o
    -- counterfactual D32: a write through a pattern variable (a strict extension of the
    -- block's scrutinee by `.1`) is not seen as a use of the scrutinee's place
    if !(← get).cfg.patternWritesVisible && (k == .borrow || k == .assign) then
      if let some sp := scrut then
        if placePrefix sp q && !(placeEq sp q) then continue
    let b := (← get).env[f]!.binds[nb - 1 - o]!
    let whole := q matches .var _
    let isBorrowVar := b.val.isBorrow || (b.ty matches some (.tRef _))
    let mode :=
      if whole && isBorrowVar && (k == .read || k == .assign) then 2
      else if whole && moved.any (· == .var o) then 2
      else if k == .borrow || k == .assign then 1
      else 0
    uses := uses.push (q, mode)
    wholeUses := wholeUses.push (q, k)
  -- maximal prefixes: places with no strict prefix among the used places
  let mut caps : Array (Place × Nat) := #[]
  for (q, _) in uses do
    let hasPrefix := uses.any fun (q', _) => placePrefix q' q && !(placeEq q' q)
    if !hasPrefix && !(caps.any fun (c, _) => placeEq c q) then
      let mode := (uses.filter fun (p, _) => placePrefix q p).foldl (fun m (_, k) => max m k) 0
      caps := caps.push (q, mode)
  -- D53 (fuzz-port Q): a place some arm moved out whole that is a strict prefix of captures
  -- (a closure in an arm capturing `q0` for its `q0.1`) is moved in whole, covering them
  for m in moved do
    if caps.any (fun (c, _) => placePrefix m c && !placeEq m c) then
      caps := (caps.filter fun (c, _) => !placePrefix m c).push (m, 2)
  -- D53 (fuzz-port M2): a capture that some arm moves out whole is moved in, whatever it is
  -- (`*x0`, `n1.1`), as the direct path moves it
  caps := caps.map fun (q, k) => if moved.any (placeEq · q) then (q, 2) else (q, k)
  -- a proof is never taken by `&` (D48 (1): only data is borrowed): its value is `⋆`, so an
  -- arm's write through a pattern variable of a matched proof (a field, a fresh value by
  -- D49 (3), in a proof position by D45) is local to the block's own copy (R8, fuzz-port)
  caps ← caps.mapM fun (q, k) => do
    if k == 1 && (← tryCatch (do isPropV (← placeType q)) (fun _ => pure false)) then pure (q, 0) else pure (q, k)
  -- D53 (fuzz-port shape (a), N3): the block's captures mirror the direct path's effects,
  -- per sub-place. A capture part of which some arm moves out is split into its fields,
  -- each captured by its own mode (moved, `&`, or read in place), so that `q1.1` can be
  -- moved while `q1.2` is lent; the block's matches on the split place take the arm of its
  -- constructor. A place used whole otherwise than as a scrutinee is moved in whole.
  let mut split : List (Place × Option Nat) := []
  let mut todo := caps.toList
  let mut out : Array (Place × Nat) := #[]
  while !todo.isEmpty do
    let (q, k) := todo.head!
    todo := todo.tail!
    let inner := moved.filter fun m => placePrefix q m && !(placeEq m q)
    if k == 2 || inner.isEmpty then out := out.push (q, k); continue
    if wholeUses.any (fun (p, pk) => placeEq p q && pk != .scrut) then out := out.push (q, 2); continue
    let children : Option (Option Nat × List Place) ← match ← content q with
      | .ind t c _ _ fs => do
        let names ← tryCatch (do
            let d ← lookupInd t
            pure ((d.ctors[c]?.map (·.2.map (·.1))).getD [])) fun _ => pure []
        pure (some (some c, fs.zipIdx.map fun (_, i) => Place.field ⟨t, c, i, names.getD i s!"f{i}"⟩ q))
      | .succ _ => pure (some (none, [Place.fst q]))
      | _ => pure none
    match children with
    | none => out := out.push (q, 2)
    | some (ctor, chs) =>
      split := (q, ctor) :: split
      for ch in chs do
        let under := uses.filter fun (p, _) => placePrefix ch p
        if under.isEmpty && !(moved.any fun m => placePrefix ch m) then continue
        let m := under.foldl (fun m (_, k) => max m k) 0
        todo := todo ++ [(ch, if moved.any (placeEq · ch) then 2 else m)]
  caps := out
  -- D53 (fuzz-port M2b, N2): a borrow variable the block moves in whole is ended by the
  -- block's frame, so an arm that moves out through it (and does not restore it) leaves it
  -- partly moved when it ends
  for (q, k) in caps do
    if let .var o := q then
      let b := (← get).env[f]!.binds[nb - 1 - o]!
      if k == 2 && (b.val.isBorrow || (b.ty matches some (.tRef _))) &&
          moved.any (fun m => m.root == o && m.steps.2.head? == some .deref) then
        err s!"[D53] a borrow ends while its content is partly moved out ({b.hint.name}: moved into a stuck match whose arm moves out through it)"
  -- order the captures by frame position (oldest binding first), then by path
  let capsS := caps.qsort fun (a, _) (b, _) => a.root > b.root || (a.root == b.root && (a.steps.2.length < b.steps.2.length))
  let n := capsS.size
  let mut hints := #[]
  let mut doms := #[]
  let mut args := #[]
  let mut pflags := #[]
  for (q, mode) in capsS do
    let T ← placeType q
    repackAt q T "captured whole by a stuck match"
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
    | 1 =>
      -- D48 (1): the block borrows the place, so its type must be known to be data (a place
      -- whose type is stuck, `⌈T(σ)⌉`, may be a universe at some instance: reviewer-6's A12)
      if (← get).cfg.refData && !(← isDataType T) then
        err s!"[D48] a stuck match would borrow {← ppPlace q}, whose type {T} is not known to be a data type"
      doms := doms.push (.tRef T); args := args.push (Term.borrow q)
    | _ =>
      -- D53: a place the block only reads is read in place, not consumed
      doms := doms.push T
      args := args.push (.prim "inplace" [Term.place q])
  let capsL := capsS.toList
  let mt := if split.isEmpty then mt else mt.selectArms (fun p => (split.find? (placeEq ·.1 p)).map (·.2)) 0
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
  let cls? := if cfg.erasureByDecl then some (if allProof then 2 else 0) else none
  let (v, _) ← evalCall false (.val anon) args.toList false cls?
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

/-- [Obs] is stated with the typing judgement wherever `Id` is evaluated (D63, rule-audit item
9). In an untyped run (a callee's body, a sealed program's re-run) the side runs in the
machine, which computes the same value as typing whenever it is not stuck; if it is stuck, it
is observed again with the typing judgement, so its stuck match is split and closed off as a
block, as when the same `Id` is formed directly. (Typing from the start would need the type of
every value in an untyped frame, which `⋆` and `⊥` do not have.) Off (`typedObs`): a stuck
side makes the `Id` stuck. -/
partial def observeTyping (typed : Bool) (t : Term) (A : Value) (W : List Pos) : M (Value × List Value) := do
  if typed || !(← get).cfg.typedObs then return ← observe typed t A W
  tryCatch (observe false t A W) fun e => match e with
    | .stuck fu _ => do modify (fun s => { s with fuel := fu }); observe true t A W
    | .error m => throw (.error m)

/-- `Id A t u ≡ And(Eq A r r', And(Eq T₁ w₁ w'₁, …))` over the result and the owners in
`W = W(t, u)` (just `Eq A r r'` when `W` is empty), both sides from the same Ω on
independent copies (v2.1, D52: directly, not through a pair, so `A` may be any borrow-free
type, a proposition or a universe included). -/
partial def idType (typed : Bool) (A t u : Term) : M Value := do
  let A' ← evalType A
  if A'.typeHasRef then err s!"Id at {A'}: A must be borrow-free (RULES §4)"
  let st ← get
  let W := footprint st.env [t, u] st.cfg.multiOwner
  let (a, as) ← observeTyping typed t A' W
  let (b, bs) ← observeTyping typed u A' W
  -- an owner's type: its binding's, else its content's. An untyped owner that is lent out
  -- now (a sealed program's re-run binding a cell that a returned borrow still holds: R1's
  -- residual) is typed by what the observation read from it, once every borrow had ended
  let Ts ← W.zipIdx.mapM fun (p, i) => do
    match ← tyAt p with
    | some T => pure T
    | none =>
      tryCatch (valType (← getAt p)) fun e =>
        tryCatch (valType as[i]!) fun _ => tryCatch (valType bs[i]!) fun _ => throw e
  -- D64 [Repack]: `Id` observes its result and owners whole
  if typed then
    for (T, (x, y)) in (A', (a, b)) :: Ts.zip (as.zip bs) do
      repackCheck "Id observes it" x T
      repackCheck "Id observes it" y T
  let eqs ← ((A', (a, b)) :: Ts.zip (as.zip bs)).mapM fun (T, (x, y)) => mkEqM T x y
  pure (andList eqs)

-- ### Typing: [Def], [Split] in tail position

/-- D61 `split`: the name of a sealed program's head call (the call [Seal] marks as the
head; one per sealed program), if it is a top-level function. -/
partial def sealedHead : Term → Option String
  | .call (.val (.gfn n)) _ true => some n
  | .call f as _ => (f :: as).findSome? sealedHead
  | .letIn _ a b | .seq a b => sealedHead a <|> sealedHead b
  | .assign _ a => sealedHead a
  | _ => none

/-- D61: the neutral that a run of the sealed program `t` is stuck on: re-run `t` as [Seal]
does and report the content of the scrutinee of the match it stopped at, if any. -/
partial def stuckScrutinee (t : Term) : M (Option Value) := do
  let saved ← get
  modify fun s => { s with env := #[{}], depth := s.depth + 1 }
  let r ← tryCatch (do discard (withErased (eval false t)); pure none) fun e =>
    match e with
    | .stuck f on => do modify (fun s => { s with fuel := f }); pure on
    | .error _ => pure none
  restoreKeep saved
  pure r

/-- D61: the sealed programs of a value, in pre-order, left to right. -/
partial def sealedIn (v : Value) : List Term :=
  match v with
  | .sealed t => t :: termVals t
  | .succ w | .borrow _ w | .tRef w => sealedIn w
  | .tEq A a b => sealedIn A ++ sealedIn a ++ sealedIn b
  | .clo cs _ | .tPi cs _ => cs.flatMap sealedIn
  | .ind _ _ _ ps fs => ps.flatMap sealedIn ++ fs.flatMap sealedIn
  | .tInd _ as => as.flatMap sealedIn
  | _ => []
where
  termVals : Term → List Term
    | .val w => sealedIn w
    | .call f as _ => termVals f ++ as.flatMap termVals
    | .letIn _ a b | .seq a b => termVals a ++ termVals b
    | .assign _ a => termVals a
    | .prim _ as => as.flatMap termVals
    | _ => []

/-- D61 `split f`: find the neutral to split. Walk the goal's sealed programs in pre-order,
left to right; from each, follow the chain of scrutinees its run is stuck on (each link
the content of the scrutinee of the match the previous one stopped at) while they are
sealed programs; the first sealed scrutinee whose head call is `f` is the one. A link may
also be an abstract value that stands for a sealed program generalised earlier (a D34
record, which re-derivations of the program are replaced by): if that program's head
call is `f`, it is the one, already generalised. -/
partial def findSplit (f : String) (G : Value) : M (Option Value) := do
  for t in sealedIn G do
    let mut cur := t
    for _ in [0:64] do
      match ← stuckScrutinee cur with
      | some n@(.sealed t') =>
        if sealedHead t' == some f then return some n
        cur := t'
      | some a@(.abs σ) =>
        match (← get).neutrals.find? (·.2 == σ) with
        | some (.sealed t', _) => if sealedHead t' == some f then return some a
        | _ => pure ()
        break
      | _ => break
  pure none

/-- D61: generalise a neutral found in the goal to a fresh `σ` of type `T`, as [Split] does
for a sealed scrutinee (D34, D37), and return `σ`. -/
partial def generalizeFound (n : Value) (T : Value) : M Nat := do
  let σ ← freshAbs T
  trace fun _ => s!"[Split] generalise {n} to σ{σ} : {T}"
  substEnv n (.abs σ) true
  if (← get).cfg.genConsistent then
    modify fun s => { s with neutrals := (n, σ) :: s.neutrals }
  pure σ

/-- D61: the neutral `split f` splits and its type, or an error. -/
partial def splitTarget (f : String) : M (Nat × Value) := do
  unless (← get).cfg.generalize do
    err s!"split {f}: it generalises a sealed program, which is switched off (RULES §5 splits only on σ)"
  let some G := (← get).goal | err "split: no goal"
  let some n := ← findSplit f G
    | err s!"split {f}: the goal {G} is not stuck on the result of a call of {f}"
  if let .abs σ := n then return (σ, ← absType σ)     -- generalised already
  let .sealed t := n | err "internal: split target"
  let some T := ← sealedResultType? t
    | err s!"split {f}: the type of {n} is not known (its head's result type depends on the arguments)"
  pure (← generalizeFound n T, T)

/-- Check a term in tail position. At the end of every path, `k` gets the result and
its type (in that path's refined state). A match on an abstract `σ` here is split:
each arm is checked to the end under its refinement ([Split]). -/
partial def checkTail (t : Term) (k : Value → Value → M Unit) : M Unit := do
  match t with
  | .prim "split" [.const f, u] =>
    -- D61: `split f in u`: split the goal's stuck result of `f`, `u` in every arm
    let (σ, T) ← splitTarget f
    let saved ← get
    match T with
    | .tNat =>
      refine σ .zero
      trace fun _ => s!"[Split] σ{σ} := 0"
      checkTail u k
      restoreArm saved
      let σ' ← freshAbs .tNat
      refine σ (.succ (.abs σ'))
      trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
      checkTail u k
      restoreArm saved
    | .tInd n ps =>
      let d ← lookupInd n
      for c in List.range d.ctors.length do
        let r ← ctorRefinement d ps c
        refine σ r
        trace fun _ => s!"[Split] σ{σ} := {r}"
        checkTail u k
        restoreArm saved
    | _ => err s!"split {f}: its result type {T} is not an inductive type"
  | .prim "splitArms" [.const f, .letIn h _ w] =>
    -- D61: `split f { C(x̄) => u, … }`: the split value is bound to a hidden variable, and
    -- the arms are an ordinary match on it
    let (σ, T) ← splitTarget f
    pushBind h (some T) (.abs σ) false
    checkTail w fun r R => do
      let fl ← getFlags
      pushTemp r
      dropTopBind
      setFlags fl
      k (← popTemp) R
  | .prim "rewrite" [h, u] | .prim "rewriteR" [h, u] =>
    -- D60: in tail position the rewritten goal becomes the path's goal, so `u` may split
    let some G := (← get).goal | err "rewrite: no goal"
    let G' ← rewriteGoal (t matches .prim "rewriteR" _) h G
    modify fun s => { s with goal := some G' }
    checkTail u k
  | .letIn h u w =>
    let es := (← get).effects.size
    let du ← if (← get).cfg.prePass then withLive true (declOf false [] [] u) else pure .other
    let (v, T) ← eval true u
    flushPending es     -- D41: the tail judgement is not an erased context
    pushBind h T v (← getFlags).2 (← refineDecl du T v)
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
    natScrutinee p
    accessPath p
    accessNeutralHead p
    match ← matchContent p with
    | .zero => checkTail z k
    | .succ _ => checkTail s k
    | .abs σ =>
      let saved ← get
      refine σ .zero
      trace fun _ => s!"[Split] σ{σ} := 0"
      checkTail z k
      restoreArm saved
      let σ' ← freshAbs .tNat
      refine σ (.succ (.abs σ'))
      trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
      checkTail s k
      restoreArm saved
    | v@(.sealed _) | v@(.loan _) =>
      discard (generalizeNeutral p v)
      checkTail t k
    | _ =>
      let (v, T) ← eval true t
      k v T.get!
  | .matchInd p ty arms =>
    abstractMatchCheck p ty
    if ← byTypeMatch ty arms then
      -- D45 (v2.0): [Split] on a proof is by its type: each arm is checked, with the fields
      -- as places holding ⋆ and no refinement; no arms, no paths
      accessPath p
      let v ← matchContent p
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
          restoreArm saved
      return
    accessPath p
    accessNeutralHead p
    match ← matchContent p with
    | .ind t c _ _ _ =>
      if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
      discard (scrutType p ty)
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
        restoreArm saved
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
  -- the body is the checked program (D64: its [Repack] points are checked, and the borrow
  -- parameters' borrows end with their values repacked when the frame pops)
  modify fun s => { s with typing := true }
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
  let (pds, cd) ← paramDecls cs hs ds c
  pushFrame
  pushCaps cs
  let mut entries := #[]
  for (((d, h), p), pd) in ((ds.zip hs).zip pf).zip pds do
    let A ← evalType d
    match A with
    | .tRef T =>
      let c ← absOf T
      let l ← freshLoan
      modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
      pushBind h (some A) (.borrow l c) p pd (d matches .val (.tRef _))
      entries := entries.push (match c with
        | .abs σ => if T == .tNat || (T matches .tInd ..) then some σ else none
        | _ => none)
    | _ =>
      if (← get).cfg.p5 && (← get).cfg.proofParamsStar && (← isPropV A) then
        pushBind h (some A) .proof p (← refineDecl pd (some A) .proof)
        entries := entries.push none
      else
        let c ← absOf A
        pushBind h (some A) c p (← refineDecl pd (some A) c)
        entries := entries.push (match c with
          | .abs σ => if A == .tNat || (A matches .tInd ..) then some σ else none
          | _ => none)
  let goal ← evalType c
  trace fun _ => s!"[Def] {self.name}: goal {goal}"
  let F1 ← popFrameRaw
  let piTy := Value.tPi cs (.pi hs ds c)
  pushFrame
  pushCaps cs
  pushBind self (some piTy) fv false (.pi cd)
  for b in F1.binds.extract cs.length F1.binds.size do pushBind b.hint b.ty b.val b.proof b.decl b.blockRef
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
  else
    let fr : RecCtx := { fn := fv, entries, cands, uid := (← get).nextRecUid }
    modify fun s => { s with nextRecUid := s.nextRecUid + 1 }
    if (← get).cfg.recNested then
      modify fun s => { s with goal := some goal, recStack := fr :: s.recStack }
    else  -- counterfactual L3: a nested function's check starts with a fresh [Rec] context
      modify fun s => { s with goal := some goal, recStack := [fr] }
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
  -- D53 (b): the body of a function whose calls are erased is an erased term
  -- (tracked with or without D53: K2/K3 read it too)
  let bodyCopies ← pure ((← fnClass piTy) != 0)
  withErasedIf bodyCopies <| checkTail body fun v T => do
    wholeReturned v
    repackCheck s!"{self.name} returns it" v T
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

end

end Ochr
