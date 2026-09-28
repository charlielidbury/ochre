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
  | .pair a b => (firstBorrowLabel a).orElse fun _ => firstBorrowLabel b
  | _ => none

/-- What a call's result type is, for [Close]'s table and for P5. -/
inductive Kind where
  | prop | unit | ref | data
deriving BEq, Inhabited

/-- A syntactic guess at whether a type term denotes a proposition. -/
partial def isPropTerm? : Term → Option Bool
  | .id .. | .eq .. | .top | .and .. => some true
  | .nat | .unit | .ref _ | .prod .. | .sort _ => some false
  | .pi _ _ c => isPropTerm? c
  | _ => none

def syntacticKind? : Term → Option Kind
  | .unit => some .unit
  | .ref _ => some .ref
  | t => (isPropTerm? t).map fun b => if b then .prop else .data

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
  | .fix _ _ ds cod b => (ds.zipIdx.all fun (d, i) => headOnly isSelf (c + i) d)
      && headOnly isSelf (c + ds.length) cod && headOnly isSelf (c + ds.length + 1) b
  | .call f as _ => headOnly isSelf c f && as.all (headOnly isSelf c)
  | .seq t u | .prod t u | .pair t u | .and t u | .andI t u | .cong t u | .ascribe t u =>
      headOnly isSelf c t && headOnly isSelf c u
  | .succ t | .fst t | .snd t | .ref t => headOnly isSelf c t
  | .eq a b d | .id a b d => headOnly isSelf c a && headOnly isSelf c b && headOnly isSelf c d
  | .prim _ as => as.all (headOnly isSelf c)
  | _ => true

/-- Same check for a top-level definition, whose self-reference is `const name`. -/
partial def constHeadOnly (n : String) : Term → Bool
  | .call (.const _) as _ => as.all (constHeadOnly n)
  | .const m => m != n
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => constHeadOnly n t
  | .letIn _ t u | .seq t u | .prod t u | .pair t u | .and t u | .andI t u | .cong t u
  | .ascribe t u => constHeadOnly n t && constHeadOnly n u
  | .matchNat _ z s => constHeadOnly n z && constHeadOnly n s
  | .pi _ ds c => ds.all (constHeadOnly n) && constHeadOnly n c
  | .fix _ _ ds c b => ds.all (constHeadOnly n) && constHeadOnly n c && constHeadOnly n b
  | .call f as _ => constHeadOnly n f && as.all (constHeadOnly n)
  | .eq a b d | .id a b d => constHeadOnly n a && constHeadOnly n b && constHeadOnly n d
  | .prim _ as => as.all (constHeadOnly n)
  | _ => true

/-- The refined entry value of `σ`: `σ` with the [Split] refinements made so far
substituted, recursively. -/
partial def expandRefs (refs : List (Nat × Value)) : Value → Value
  | .abs σ => match refs.lookup σ with
      | some r => expandRefs refs r
      | none => .abs σ
  | .succ v => .succ (expandRefs refs v)
  | v => v

/-- The strict subterms of a value built from `S`. -/
def strictSubterms : Value → List Value
  | .succ v => v :: strictSubterms v
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
  | .pair a b => return .pair (← substV x r a) (← substV x r b)
  | .borrow l w => return .borrow l (← substV x r w)
  | .clo cs t => return .clo (← cs.mapM (substV x r)) (← substT x r t)
  | .tPi cs t => return .tPi (← cs.mapM (substV x r)) (← substT x r t)
  | .sealed t => nfSealed (← substT x r t)
  | .tProd A B => return .tProd (← substV x r A) (← substV x r B)
  | .tEq A a b => return mkEq (← substV x r A) (← substV x r a) (← substV x r b)
  | .tAnd P Q => return mkAnd (← substV x r P) (← substV x r Q)
  | .tRef A => return .tRef (← substV x r A)
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
  | .fix h hs ds c b => return .fix h hs (← ds.mapM go) (← go c) (← go b)
  | .call f as hd => return .call (← go f) (← as.mapM go) hd
  | .succ u => return .succ (← go u)
  | .fst u => return .fst (← go u)
  | .snd u => return .snd (← go u)
  | .ref u => return .ref (← go u)
  | .prod a b => return .prod (← go a) (← go b)
  | .pair a b => return .pair (← go a) (← go b)
  | .and a b => return .and (← go a) (← go b)
  | .andI a b => return .andI (← go a) (← go b)
  | .cong a b => return .cong (← go a) (← go b)
  | .ascribe a b => return .ascribe (← go a) (← go b)
  | .eq a b c => return .eq (← go a) (← go b) (← go c)
  | .id a b c => return .id (← go a) (← go b) (← go c)
  | .prim n as => return .prim n (← as.mapM go)
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
  modify fun s => { s with env := #[{}] }
  let r ← tryCatch (do let (v, _) ← eval false t; pure (some v)) fun e =>
    match e with
    | .stuck f => do modify (fun s => { s with fuel := f }); pure none
    | .error m => throw (.error m)
  restoreKeep saved
  match r with
  | some v => pure v
  | none => pure (.sealed t)

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

/-- [Read]: borrow-free content is copied; a borrow is moved out (`p ↦ ⊥`). -/
partial def readPlace (p : Place) : M Value := do
  accessPath p; accessInside p
  let v ← content p
  match v with
  | .bot => err s!"[Read] {← ppPlace p} was moved out or its borrow ended (reading ⊥)"
  | .borrow _ _ => setPlace p .bot; pure v
  | _ => pure v

/-- [Borrow] `&p ⇓ borrow_ℓ v` with `p ↦ loan_ℓ`. -/
partial def borrowPlace (p : Place) : M Value := do
  accessPath p; accessInside p
  let v ← content p
  match v with
  | .bot => err s!"[Borrow] {← ppPlace p} was moved out (borrowing ⊥)"
  | .borrow _ _ => err "[Borrow] a borrow of a borrow (&&T is outside the core)"
  | _ =>
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
    | .tProd A _ => pure A
    | T => err s!"{← ppPlace q}.1: no sub-place at type {T}"
  | .snd q => match ← placeType q with
    | .tProd _ B => pure B
    | T => err s!"{← ppPlace q}.2: no sub-place at type {T}"

/-- The type of a value, for untyped bindings (captured values) and embedded values. -/
partial def valType (v : Value) : M Value := do
  match v with
  | .zero | .succ _ => pure .tNat
  | .unit => pure .tUnit
  | .pair a b => pure (.tProd (← valType a) (← valType b))
  | .abs σ => absType σ
  | .gfn n => pure (← lookupGlobal n).ty
  | .clo cs (.fix _ hs ds c _) => pure (.tPi cs (.pi hs ds c))
  | .borrow _ w => pure (.tRef (← valType w))
  | .tNat | .tUnit | .tProd .. | .tEq .. | .tTop | .tAnd .. | .tRef _ | .tPi .. | .sort _ =>
    pure (.sort (← sortOf v))
  | _ => err s!"cannot infer the type of the value {v}"

/-- The universe level of a type value: `0` is `Prop`. -/
partial def sortOf (T : Value) : M Nat := do
  match T with
  | .tNat | .tUnit | .tRef _ => pure 1
  | .tProd A B => pure (max 1 (max (← sortOf A) (← sortOf B)))
  | .tEq .. | .tTop | .tAnd .. => pure 0
  | .sort l => pure (l + 1)
  | .abs σ => match ← absType σ with
    | .sort l => pure l
    | S => err s!"σ{σ} : {S} is not a type"
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
  | .tEq .. | .tTop | .tAnd .. => pure true
  | .tNat | .tUnit | .tRef _ | .tProd .. | .sort _ => pure false
  | .tPi _ (.pi _ _ c) => match isPropTerm? c with
    | some b => pure b
    | none => pure ((← sortOf T) == 0)
  | .abs σ => pure ((← absType σ) == .sort 0)
  | _ => pure false

/-- A value standing for an arbitrary inhabitant of `A`, used only to compute sorts. -/
partial def genericValue (A : Value) : M Value := do
  if (← get).cfg.p5 && (← isPropV A) then return .proof
  match A with
  | .tRef T => pure (.borrow (← freshLoan) (.abs (← freshAbs T)))
  | _ => pure (.abs (← freshAbs A))

/-- Evaluate a type (P2: once, against the current Ω, on a private copy). -/
partial def evalType (t : Term) : M Value := onCopy do
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
  let t' := t.mapFree (fun c o => .var (c + m - 1 - idx o)) 0
  pure (vals.toList, t')

-- ### Evaluation

partial def expectTy (what : String) (T : Option Value) (A : Value) : M Unit := do
  if let some T := T then
    unless T == A do err s!"{what} has type {T}, expected {A}"

partial def eval (typed : Bool) (t : Term) : M (Value × Option Value) := do
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
    pushBind h T v
    let (r, R) ← eval typed w
    pushTemp r
    dropTopBind
    pure (← popTemp, R)
  | .seq u w =>
    let (v, _) ← eval typed u
    dropValue v
    eval typed w
  | .matchNat p z s => evalMatch typed p z s
  | .const n =>
    let g ← lookupGlobal n
    let v ← if (← get).cfg.p5 && (← isPropV g.ty) then pure .proof else pure g.val
    pure (v, some g.ty)
  | .val v =>
    if typed then pure (v, some (← valType v)) else pure (v, none)
  | .sort l => pure (.sort l, some (.sort (l + 1)))
  | .pi .. =>
    let (cs, t') ← capture t
    let T := Value.tPi cs t'
    if typed then pure (T, some (.sort (← sortOf T))) else pure (T, none)
  | .fix _ hs ds c _ =>
    let (cs, t') ← capture t
    let v := Value.clo cs t'
    let T := match t' with
      | .fix _ _ ds' c' _ => Value.tPi cs (.pi hs ds' c')
      | _ => Value.tPi cs (.pi hs ds c)
    if typed then checkFix v cs t'
    let v ← if (← get).cfg.p5 && (← isPropV T) then pure .proof else pure v
    pure (v, some T)
  | .call f as hd => evalCall typed f as hd
  | .nat => pure (.tNat, some (.sort 1))
  | .unit => pure (.tUnit, some (.sort 1))
  | .top => pure (.tTop, some (.sort 0))
  | .zero => pure (.zero, ty .tNat)
  | .tt => pure (.unit, ty .tUnit)
  | .succ u =>
    let (v, T) ← eval typed u
    expectTy "the argument of S" T .tNat
    pure (.succ v, ty .tNat)
  | .prod a b => onCopy do
    let A ← evalType a
    let B ← evalType b
    pure (.tProd A B, some (.sort (← sortOf (.tProd A B))))
  | .pair a b =>
    let (v, A) ← eval typed a
    pushTemp v
    let (w, B) ← eval typed b
    let v ← popTemp
    if let (some A, some B) := (A, B) then
      if A.typeHasRef || B.typeHasRef then err "a pair holding a borrow (no borrows inside data, RULES §1)"
    pure (.pair v w, match A, B with | some A, some B => some (.tProd A B) | _, _ => none)
  | .fst u | .snd u =>
    let (v, T) ← eval typed u
    let first := t matches .fst _
    let r ← match v with
      | .pair a b => pure (if first then a else b)
      | .abs _ | .sealed _ => if typed then err "projection of a neutral pair (no neutral projections in v1)" else stuckNow
      | _ => err s!"projection of a non-pair {v}"
    let R := match T with
      | some (.tProd A B) => some (if first then A else B)
      | _ => none
    pure (r, R)
  | .eq A a b => onCopy do
    let A' ← evalType A
    let (va, Ta) ← eval typed a
    let (vb, Tb) ← eval typed b
    expectTy "the left side of Eq" Ta A'
    expectTy "the right side of Eq" Tb A'
    pure (mkEq A' va vb, some (.sort 0))
  | .refl => pure (.proof, ty .tTop)
  | .and P Q => onCopy do
    let P' ← evalType P
    let Q' ← evalType Q
    pure (mkAnd P' Q', some (.sort 0))
  | .andI h k =>
    let (_, Th) ← eval typed h
    let (_, Tk) ← eval typed k
    pure (.proof, match Th, Tk with | some a, some b => some (mkAnd a b) | _, _ => none)
  | .cong f h =>
    let (fv, fT) ← eval typed f
    let (_, Th) ← eval typed h
    if !typed then return (.proof, none)
    match Th with
    | some .tTop => pure (.proof, some .tTop)
    | some (.tEq A a b) =>
      let (fa, B) ← callFn true fv fT #[a] #[some A] false
      let (fb, _) ← callFn true fv fT #[b] #[some A] false
      pure (.proof, some (mkEq B.get! fa fb))
    | some T => err s!"cong: the proof has type {T}, which is not an equation"
    | none => err "cong: untyped proof"
  | .ref A =>
    let A' ← evalType A
    if A'.typeHasRef then err "&A needs A borrow-free (RULES §1)"
    pure (.tRef A', some (.sort 1))
  | .id A a b => pure (← idType typed A a b, some (.sort 0))
  | .prim "J" [_, P, h, u] =>
    -- transport: the value is unchanged; the type moves from `P a` to `P b`
    let (Pv, PT) ← eval typed P
    let (_, Th) ← eval typed h
    let (v, Tu) ← eval typed u
    if !typed then return (v, none)
    match Th with
    | some .tTop => pure (v, Tu)
    | some (.tEq A a b) =>
      let (Pa, _) ← callFn true Pv PT #[a] #[some A] false
      expectTy "the transported term" Tu Pa
      let (Pb, _) ← callFn true Pv PT #[b] #[some A] false
      pure (v, some Pb)
    | _ => err s!"J: the proof has type {Th.getD .bot}, which is not an equation"
  | .prim "symm" [h] =>
    let (_, Th) ← eval typed h
    match Th with
    | some (.tEq A a b) => pure (.proof, some (mkEq A b a))
    | some .tTop => pure (.proof, some .tTop)
    | _ => if typed then err "symm: not an equation" else pure (.proof, none)
  | .prim "trans" [h, k] =>
    let (_, Th) ← eval typed h
    let (_, Tk) ← eval typed k
    if !typed then return (.proof, none)
    match Th, Tk with
    | some .tTop, some T | some T, some .tTop => pure (.proof, some T)
    | some (.tEq A a b), some (.tEq A' b' c) =>
      unless A == A' && b == b' do err s!"trans: {Th.get!} and {Tk.get!} do not compose"
      pure (.proof, some (mkEq A a c))
    | _, _ => err "trans: not equations"
  | .prim n _ => err s!"unknown primitive {n}"
  | .ascribe u A =>
    if !typed then return (← eval false u)
    let A' ← evalType A
    let (v, T) ← eval true u
    expectTy "the ascribed term" T A'
    pure (v, some A')

-- ### Calls: [Call], P5, [Call-type], [Close], [Rec]

partial def evalCall (typed : Bool) (f : Term) (as : List Term) (head : Bool) :
    M (Value × Option Value) := do
  let (fv, fT) ← eval typed f
  pushTemp fv
  let mut tys := #[]
  for a in as do
    let (w, T) ← eval typed a
    pushTemp w
    tys := tys.push T
  let ws ← popTemps as.length
  let fv ← popTemp
  callFn typed fv fT ws tys head

/-- The Π-type of a function value. -/
partial def funType (fv : Value) (fT : Option Value) : M Value := do
  if let some T := fT then return T
  match fv with
  | .gfn n => pure (← lookupGlobal n).ty
  | .clo cs (.fix _ hs ds c _) => pure (.tPi cs (.pi hs ds c))
  | .abs σ => absType σ
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

/-- [Call-type]: the result type is `B` evaluated at the call point (after the
arguments are evaluated) with each parameter bound to its argument's value (a borrow
argument moved into it). The other free variables of `B` were captured when the
Π-type was formed. Each argument is checked against its parameter's type. -/
partial def callType (piTy : Value) (ws : Array Value) (tys : Array (Option Value)) : M Value := do
  let .tPi cs (.pi hs ds c) := piTy | err s!"not a function type: {piTy}"
  if ds.length != ws.size then err s!"arity: {ds.length} parameters, {ws.size} arguments"
  onCopy do
    pushFrame
    for v in cs do pushBind ⟨"κ"⟩ none v
    for ((d, h), i) in (ds.zip hs).zipIdx do
      let A ← evalType d
      expectTy s!"argument {i + 1} ({h.name})" tys[i]! A
      pushBind h (some A) ws[i]!
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
  let .fix self hs _ _ body := t | err "internal: not a fix"
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  pushBind self none fv
  for (h, w) in hs.zip ws.toList do pushBind h none w
  let (v, _) ← eval false body
  pushTempAt ((← topIdx) - 1) v
  popFrame
  popTemp

partial def callFn (typed : Bool) (fv : Value) (fT : Option Value) (ws : Array Value)
    (tys : Array (Option Value)) (head : Bool) : M (Value × Option Value) := do
  if (← get).cfg.argNotBot then
    if let some i := ws.findIdx? (· == .bot) then
      err s!"[Call] argument {i + 1} is ⊥ at the call point (a later argument ended its borrow): an argument not of the parameter's type"
  -- A proof value is only ever called at a proposition: P5, not run.
  if fv == .proof then
    let B ← if typed then some <$> callType (← funType fv fT) ws tys else pure none
    endBorrowArgs ws
    return (.proof, B)
  let piTy ← funType fv fT
  let B ← if typed then some <$> callType piTy ws tys else pure none
  if typed then
    trace fun _ => s!"[Call-type] {fv}({", ".intercalate (ws.toList.map toString)}) : {B.getD .bot}"
    recCheck fv ws
  let kind ← match B with
    | some B => kindOf B
    | none => resultKind piTy ws
  if kind == .prop && (← get).cfg.p5 then
    endBorrowArgs ws
    return (.proof, B)
  match fv with
  | .abs _ => pure (← closeCall fv ws kind, B)
  | .gfn _ | .clo _ _ =>
    let (cs, t) ← fixOf fv
    let r ← tryCatch (runBody fv cs t ws) fun e =>
      match e with
      | .stuck fu =>
        if head then throw e
        else do
          modify fun s => { s with fuel := fu }
          closeCall fv ws kind
      | .error m => throw (.error m)
    pure (r, B)
  | _ => err s!"call of {fv}, which is not a function"

/-- [Close]: the call `f(w̄)` has a stuck body; the partial run has been discarded (the
state is back at the call point). `L := let cᵢ = uᵢ`, `C := f(ā)` with `aᵢ = &cᵢ` for
the borrow arguments `wᵢ = borrow_ℓᵢ uᵢ`; the result and the loans follow the table. -/
partial def closeCall (fv : Value) (ws : Array Value) (kind : Kind) : M Value := do
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
      substEnv (.loan l) (.sealed fill) false
    pure (.borrow k (.sealed (wrapL (.letIn ⟨"r"⟩ (C 0) (.place (.deref (.var 0)))))))
  | _ =>
    for ((_, l, _), j) in bs.zipIdx do
      substEnv (.loan l) (.sealed (wrapL (.seq (C 0) (cell 0 j)))) false
    pure (if kind == .unit then .unit else .sealed (wrapL (C 0)))

/-- [Rec]: at a recursive call, a parameter position survives if its argument (the
content, through a borrow) is a strict subterm of that parameter's entry value as
refined so far. The recursive position is any position that survives every call. -/
partial def recCheck (fv : Value) (ws : Array Value) : M Unit := do
  let st ← get
  let some ctx := st.recCtx | return
  unless ctx.fn == fv do return
  if !st.cfg.recGuard then return
  let cands := st.recCands.filter fun j =>
    match ctx.entries[j]?.join, ws[j]? with
    | some σ, some w =>
      let u := match w with | .borrow _ u => u | u => u
      (strictSubterms (expandRefs st.refs (.abs σ))).contains u
    | _, _ => false
  set { st with recCands := cands, recCalls := st.recCalls + 1 }
  -- fail at the offending call, before it is run (running it may not terminate)
  if cands.isEmpty then
    err s!"[Rec] no parameter decreases structurally in every recursive call (at {fv}({", ".intercalate (ws.toList.map toString)}): each recursive argument must be a strict subterm of that parameter's entry value as refined so far)"

-- ### Match: [Match], [Split], stuck blocks

/-- Apply a refinement `σ := r` to Ω, the stored types and the goal ([Split]). -/
partial def refine (σ : Nat) (r : Value) : M Unit := do
  substEnv (.abs σ) r true
  modify fun s => { s with refs := (σ, r) :: s.refs }

partial def evalMatch (typed : Bool) (p : Place) (z s : Term) : M (Value × Option Value) := do
  accessPath p
  let v ← content p
  match v with
  | .zero => eval typed z
  | .succ _ => eval typed s
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ => if typed then splitThenClose p z s σ else stuckNow
  | .sealed _ | .loan _ =>
    if !typed then stuckNow
    else
      let σ ← generalizeNeutral p v
      splitThenClose p z s σ
  | _ => err s!"[Match] on a non-Nat value {v}"

/-- A match in the checked program on a neutral that is not an abstract value (e.g. a
sealed program left by an opaque call, deriver-e346 §E4.3): v1's [Split] covers only
`σ`. Clarification: generalise first, i.e. replace that neutral everywhere (Ω, stored
types, goal) by a fresh `σ`, then split on it. This is dependent elimination with a
generalised motive, sound in the model (meta-model §3.5); it may lose completeness. -/
partial def generalizeNeutral (p : Place) (n : Value) : M Nat := do
  unless (← get).cfg.generalize do
    err s!"[Split] on {← ppPlace p}, whose content {n} is a neutral but not an abstract value (RULES §5 splits only on σ)"
  let σ ← freshAbs .tNat
  trace fun _ => s!"[Split] generalise {n} to σ{σ}"
  substEnv n (.abs σ) true
  pure σ

/-- The free variables of a match that were moved out (became `⊥`) in an arm. -/
partial def movedIn (fvs : List Nat) (before : List Value) : M (List Nat) := do
  let mut out := []
  for (o, b) in fvs.zip before do
    let v ← getAt (← varPos o)
    if v == .bot && b != .bot then out := out ++ [o]
  pure out

/-- [Split] for a non-tail match: check each arm under its refinement, then close the
match off as a stuck block and continue once from the unrefined state (D15). -/
partial def splitThenClose (p : Place) (z s : Term) (σ : Nat) : M (Value × Option Value) := do
  let mt := Term.matchNat p z s
  let fvs := mt.freeVars
  let before ← fvs.mapM fun o => do getAt (← varPos o)
  let saved ← get
  refine σ .zero
  let (_, Tz) ← eval true z
  let mz ← movedIn fvs before
  restoreKeep saved
  let σ' ← freshAbs .tNat
  refine σ (.succ (.abs σ'))
  let (_, Ts) ← eval true s
  let ms ← movedIn fvs before
  restoreKeep saved
  let some Tz := Tz | err "internal: untyped arm"
  unless Ts == some Tz do
    err s!"the arms of a non-tail match have different types ({Tz} and {Ts.getD .bot}); v1 does not say what the closed-off match's result type is"
  closeOffMatch mt Tz (mz ++ ms)

/-- Stuck blocks (RULES §3): close a stuck match off as the body of a call to an
anonymous function of its free places. Borrow variables it uses become borrow
arguments (moved in if an arm moves them, reborrowed `&*x` otherwise); owned places it
writes become borrow arguments `&x`; places it only reads become value arguments. -/
partial def closeOffMatch (mt : Term) (B : Value) (moved : List Nat) :
    M (Value × Option Value) := do
  let occs := mt.freeOccs
  let fvs := (mt.freeVars.toArray.qsort (· > ·)).toList   -- oldest binding first
  let n := fvs.length
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
  let mut hints := #[]
  let mut doms := #[]
  let mut args := #[]
  let mut derefd : List Nat := []
  for o in fvs do
    let b := (← get).env[f]!.binds[nb - 1 - o]!
    let T ← match b.ty with
      | some T => pure T
      | none => valType b.val
    let isBorrowVar := b.val.isBorrow || (T matches .tRef _)
    let written := occs.any fun (o', _, k) => o' == o && (k == .borrow || k == .assign)
    hints := hints.push b.hint
    if isBorrowVar then
      doms := doms.push T
      args := args.push (if moved.contains o then Term.place (.var o) else .borrow (.deref (.var o)))
    else if written then
      doms := doms.push (.tRef T)
      args := args.push (.borrow (.var o))
      derefd := o :: derefd
    else
      doms := doms.push T
      args := args.push (.place (.var o))
  let idx (o : Nat) : Nat := (fvs.findIdx? (· == o)).getD 0
  let body := mt.mapFree (fun c o =>
    let v := Place.var (c + n - 1 - idx o)
    if derefd.contains o then .deref v else v) 0
  let anon := Value.clo [] (.fix ⟨"_"⟩ hints.toList (doms.toList.map .val) (.val B) body)
  let (v, _) ← evalCall false (.val anon) args.toList false
  pure (v, some B)

-- ### Observation and `Id` (RULES §4)

/-- `⟦t⟧^W`: on a private copy of Ω, run `t`, end every borrow, and return the result
paired with the final contents of the owners in `W`. -/
partial def observe (typed : Bool) (t : Term) (A : Value) (W : List Pos) : M Value := onCopy do
  let (v, T) ← eval typed t
  expectTy "a side of Id" T A
  pushTemp v
  endAll
  let v ← popTemp
  let ws ← W.mapM getAt
  pure (tupleVal v ws)

/-- `Id A t u ≡ Eq (A × T_W) ⟦t⟧^W ⟦u⟧^W`, both sides from the same Ω on independent
copies. -/
partial def idType (typed : Bool) (A t u : Term) : M Value := do
  let A' ← evalType A
  if A'.typeHasRef then err s!"Id at {A'}: A must be borrow-free (RULES §4)"
  let st ← get
  let W := footprint st.env [t, u] st.cfg.multiOwner
  let Ts ← W.mapM fun p => do
    match ← tyAt p with
    | some T => pure T
    | none => valType (← getAt p)
  let a ← observe typed t A' W
  let b ← observe typed u A' W
  pure (mkEq (tupleType A' Ts) a b)

-- ### Typing: [Def], [Split] in tail position

/-- Check a term in tail position. At the end of every path, `k` gets the result and
its type (in that path's refined state). A match on an abstract `σ` here is split:
each arm is checked to the end under its refinement ([Split]). -/
partial def checkTail (t : Term) (k : Value → Value → M Unit) : M Unit := do
  match t with
  | .letIn h u w =>
    let (v, T) ← eval true u
    pushBind h T v
    checkTail w fun r R => do
      pushTemp r
      dropTopBind
      k (← popTemp) R
  | .seq u w =>
    let (v, _) ← eval true u
    dropValue v
    checkTail w k
  | .matchNat p z s =>
    accessPath p
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
  | _ =>
    let (v, T) ← eval true t
    match T with
    | some T => k v T
    | none => err "internal: untyped result in the checker"

/-- [Def]: `fix f (x̄:Ā):B := b` is checked at its generic call. Ω has a fresh owned
place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ` (frame 0); the call is
`f(ā)` with `aᵢ = &cᵢ` or `σᵢ`; the goal is the [Call-type] of that call; the body
runs in a pushed frame and its result's type must convert to the goal as refined by
splits. Afterwards the whole state is restored. -/
partial def checkFix (fv : Value) (cs : List Value) (t : Term) : M Unit := do
  let .fix self hs ds c body := t | err "internal: not a fix"
  let saved ← get
  if (← get).cfg.selfHeadOnly then
    let n := ds.length
    unless headOnly (fun d p => p.root == d + n) 0 body do
      err s!"[Rec] {self.name} occurs in its own body other than as the head of a call (fix L1)"
  modify fun s => { s with env := #[{}], goal := none, recCtx := none, refs := [] }
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  let mut entries := #[]
  for (d, h) in ds.zip hs do
    let A ← evalType d
    match A with
    | .tRef T =>
      let σ ← freshAbs T
      let l ← freshLoan
      modifyFrame 0 fun fr => { fr with binds := fr.binds.push ⟨⟨s!"{h.name}°"⟩, some T, .loan l⟩ }
      pushBind h (some A) (.borrow l (.abs σ))
      entries := entries.push (if T == .tNat then some σ else none)
    | _ =>
      if (← get).cfg.p5 && (← isPropV A) then
        pushBind h (some A) .proof
        entries := entries.push none
      else
        let σ ← freshAbs A
        pushBind h (some A) (.abs σ)
        entries := entries.push (if A == .tNat then some σ else none)
  let goal ← evalType c
  trace fun _ => s!"[Def] {self.name}: goal {goal}"
  let F1 ← popFrameRaw
  let piTy := Value.tPi cs (.pi hs ds c)
  pushFrame
  for v in cs do pushBind ⟨"κ"⟩ none v
  pushBind self (some piTy) fv
  for b in F1.binds.extract cs.length F1.binds.size do pushBind b.hint b.ty b.val
  let cands := (entries.toList.zipIdx).filterMap fun (e, i) => e.map fun _ => i
  modify fun s => { s with goal := some goal, recCtx := some ⟨fv, entries⟩,
                            recCands := cands, recCalls := 0 }
  checkTail body fun v T => do
    pushTempAt ((← topIdx) - 1) v
    popFrame
    discard popTemp
    let g := (← get).goal.getD .bot
    trace fun _ => s!"[Def] {self.name}: path ends with type {T} against goal {g}"
    unless T == g do
      err s!"the body of {self.name} has type {T}, but the goal is {g}"
  let st ← get
  if st.cfg.recGuard && st.recCalls > 0 && st.recCands.isEmpty then
    err s!"[Rec] no parameter of {self.name} decreases structurally in every recursive call (each recursive argument must be a strict subterm of that parameter's entry value)"
  restoreKeep saved
  modify fun s => { s with recCands := saved.recCands, recCalls := saved.recCalls }

end

end Ochr
