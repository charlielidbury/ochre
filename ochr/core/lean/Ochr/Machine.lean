import Ochr.Decide

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
  block (`closeBlock`), and evaluation continues once from there.

Everything that runs the machine is in one `mutual` block, because normalising a
sealed program ([Seal]) runs the machine, substitution ([End], refinement)
normalises, and forming a type (`Id`) runs observations.
-/

namespace Ochr

/-- The fuel the checker has left: the bound that the machine's mutually recursive functions
(the evaluator, conversion, typing, closing off) and the other functions that recurse on fuel
start from at each entry from outside (all checker code is total, `ochr/core/CLAUDE.md`). Each
call into the cycle spends one unit of the bound, and running out is exhaustion, the outcome
`tick` throws ("the checker does not know"), never an answer. -/
def fuelLeft : M Nat := return (← getThe Fuel).left

/-- Print a place with the names of the top frame's bindings. -/
def ppPlace (p : Place) : M String := do
  let f ← topIdx
  let names := (← get).env[f]!.binds.toList.reverse.map (·.hint.name)
  pure (p.pp names)

/-- The content of a place, if its path exists in Ω (a total query: `none` is the answer "the
place does not exist", never a caught error). -/
def content? (p : Place) : M (Option Value) := do
  let (i, ss) := p.steps
  pure ((← getAt (← varPos i)).follow ss)

/-- The content of a place (RULES §3: follow `x`, `*p` through `borrow_ℓ v` to `v`,
`p.1` through `S v` to `v`), which must exist. -/
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

mutual
/-- Does `self` (tested by `isSelf depth term`) occur in `t` only as the head of a
call? (Fix L1 of this checker; see notes/lean-checker.md.) -/
def headOnly (isSelf : Nat → Place → Bool) (c : Nat) : Term → Bool
  | .call (.place p) as _ =>
      ((isSelf c p && (p matches .var _)) || !isSelf c p) && headOnlyList isSelf c as
  | .place p | .borrow p => !isSelf c p
  | .assign p t => !isSelf c p && headOnly isSelf c t
  | .letIn _ t u => headOnly isSelf c t && headOnly isSelf (c + 1) u
  | .matchNat p z s => !isSelf c p && headOnly isSelf c z && headOnly isSelf c s
  | .pi _ ds cod => headOnlyDoms isSelf c ds && headOnly isSelf (c + ds.length) cod
  | .fix _ _ ds cod _ b => headOnlyDoms isSelf c ds
      && headOnly isSelf (c + ds.length) cod && headOnly isSelf (c + ds.length + 1) b
  | .call f as _ => headOnly isSelf c f && headOnlyList isSelf c as
  | .seq t u | .cong t u | .ascribe t u =>
      headOnly isSelf c t && headOnly isSelf c u
  | .succ t | .fst t | .snd t | .ref t => headOnly isSelf c t
  | .eq a b d | .id a b d => headOnly isSelf c a && headOnly isSelf c b && headOnly isSelf c d
  | .ctor _ _ _ ps as => headOnlyList isSelf c ps && headOnlyList isSelf c as
  | .prim _ as | .tind _ as => headOnlyList isSelf c as
  | .matchInd p _ as => !isSelf c p && headOnlyArms isSelf c as
  | _ => true
termination_by structural t => t

/-- `ts.all (headOnly isSelf c)`. -/
def headOnlyList (isSelf : Nat → Place → Bool) (c : Nat) : List Term → Bool
  | [] => true
  | t :: ts => headOnly isSelf c t && headOnlyList isSelf c ts
termination_by structural ts => ts

/-- A match's arms. -/
def headOnlyArms (isSelf : Nat → Place → Bool) (c : Nat) : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: ts => headOnly isSelf c t && headOnlyArms isSelf c ts
termination_by structural ts => ts

/-- A telescope's domains, the `i`-th at depth `c + i`. -/
def headOnlyDoms (isSelf : Nat → Place → Bool) (c : Nat) : List Term → Bool
  | [] => true
  | d :: ds => headOnly isSelf c d && headOnlyDoms isSelf (c + 1) ds
termination_by structural ds => ds
end

mutual
/-- Same check for a top-level definition, whose self-reference is `const name`. -/
def constHeadOnly (n : String) : Term → Bool
  | .call (.const _) as _ => constHeadOnlyList n as
  | .const m => m != n
  | .assign _ t | .succ t | .fst t | .snd t | .ref t => constHeadOnly n t
  | .letIn _ t u | .seq t u | .cong t u
  | .ascribe t u => constHeadOnly n t && constHeadOnly n u
  | .matchNat _ z s => constHeadOnly n z && constHeadOnly n s
  | .pi _ ds c => constHeadOnlyList n ds && constHeadOnly n c
  | .fix _ _ ds c _ b => constHeadOnlyList n ds && constHeadOnly n c && constHeadOnly n b
  | .call f as _ => constHeadOnly n f && constHeadOnlyList n as
  | .eq a b d | .id a b d => constHeadOnly n a && constHeadOnly n b && constHeadOnly n d
  | .ctor _ _ _ ps as => constHeadOnlyList n ps && constHeadOnlyList n as
  | .prim _ as | .tind _ as => constHeadOnlyList n as
  | .matchInd _ _ as => constHeadOnlyArms n as
  | _ => true
termination_by structural t => t

/-- `ts.all (constHeadOnly n)`. -/
def constHeadOnlyList (n : String) : List Term → Bool
  | [] => true
  | t :: ts => constHeadOnly n t && constHeadOnlyList n ts
termination_by structural ts => ts

/-- A match's arms. -/
def constHeadOnlyArms (n : String) : List (Hint × Term) → Bool
  | [] => true
  | (_, t) :: ts => constHeadOnly n t && constHeadOnlyArms n ts
termination_by structural ts => ts
end

/-- `expandRefs` with an explicit bound: a refinement's value may mention abstract values
refined in turn, and nothing in the types says the chain ends, so the walk is bounded, and
running out is exhaustion, never an answer. -/
def expandRefsF (refs : List (Nat × Value)) : Nat → Value → M Value
  | 0, _ => exhausted "out of fuel"
  | fuel + 1, .abs σ => match refs.lookup σ with
      | some r => expandRefsF refs fuel r
      | none => pure (.abs σ)
  | fuel + 1, .succ v => return .succ (← expandRefsF refs fuel v)
  | fuel + 1, .ind t c h ps fs => return .ind t c h ps (← fs.mapM (expandRefsF refs fuel))
  | _ + 1, v => pure v
termination_by structural fuel _ => fuel

/-- The refined entry value of `σ`: `σ` with the [Split] refinements made so far
substituted, recursively (bounded by the fuel left: `expandRefsF`). -/
def expandRefs (refs : List (Nat × Value)) (v : Value) : M Value := do
  expandRefsF refs (← fuelLeft) v

mutual
/-- v2.0 (D46): infer an inductive's parameters by matching a field's declared type
term `FT` (in the scope of the `np` parameters) against the type `T` of the value given
for it. Only unsolved parameters are filled; the field types are checked afterwards. -/
def unifyParams (np : Nat) (FT : Term) (T : Value) (sol : Array (Option Value)) :
    Array (Option Value) :=
  match FT, T with
  | .place (.var j), _ =>
    if j < np && (sol[np - 1 - j]!).isNone then sol.set! (np - 1 - j) (some T) else sol
  | .tind m as, .tInd m' vs =>
    if m == m' && as.length == vs.length then unifyParamsList np as vs sol
    else sol
  | _, _ => sol
termination_by structural FT

/-- `unifyParams` over the arguments of `m(…)` and of its type, left to right. -/
def unifyParamsList (np : Nat) : List Term → List Value → Array (Option Value) → Array (Option Value)
  | a :: as, v :: vs, sol => unifyParamsList np as vs (unifyParams np a v sol)
  | _, _, sol => sol
termination_by structural as => as
end

mutual
/-- The strict subterms of a value built from `S`. -/
def strictSubterms : Value → List Value
  | .succ v => v :: strictSubterms v
  | .ind _ _ _ _ fs => strictSubtermsList fs
  | _ => []
termination_by structural v => v

/-- `fs.flatMap fun f => f :: strictSubterms f`. -/
def strictSubtermsList : List Value → List Value
  | [] => []
  | f :: fs => (f :: strictSubterms f) ++ strictSubtermsList fs
termination_by structural fs => fs
end

/-- D64 [Open]: a write or borrow through an index field of a dependent constructor value
invalidates the proof fields whose types mention that field: they become `⊥` until assigned
again (a proof is `⋆` and carries no type, so a stale one could not be told apart at the
repack; an assigned proof is checked against the telescope at the current contents). -/
def openWrite (p : Place) : M Unit := do
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
        if (← content? fp).isSome then
          fire .Open fun _ => s!"a write through {g.name} invalidates the proof field {fname}"
          setPlace fp .bot

/-- K2/K3: this point runs at runtime: not in an erased term, and not in model code (an
`implemented by` body or a model function's, which never runs at runtime). -/
def atRuntime : M Bool := do
  pure ((← get).erasedDepth == 0 && (← get).modelDepth == 0)

/-- K3: a match whose arms name the constructors of an abstract (or unsized) type, at runtime
outside model code. -/
def abstractMatchCheck (p : Place) (ty : String) : M Unit := do
  if ty == "" then return
  let d ← lookupInd ty
  if (d.abstract || d.unsized) && (← atRuntime) then
    err s!"[K3] a match on {← ppPlace p} with the constructors of the abstract type {ty} at runtime, outside model code"

/-- A type headed by an `unsized` declaration (K2). -/
def isUnsizedType (T : Value) : M Bool := do
  match T with
  | .tInd n _ => pure (← lookupInd n).unsized
  | _ => pure false

/-- K2: at runtime outside model code, a place whose content has an unsized type is only
borrowed: never read, moved or assigned (matching it is K3's check). The type is read off
the content (a constructor value, or an abstract value's type). -/
def unsizedCheck (p : Place) (v : Value) (what : String) : M Unit := do
  if !(← atRuntime) then return
  let T? ← match v with
    | .ind t _ _ ps _ => pure (some (Value.tInd t ps))
    | .abs σ => some <$> absType σ
    | _ => pure none
  if let some T := T? then
    if ← isUnsizedType T then
      err s!"[K2] {← ppPlace p}, of the unsized type {T}, is {what} at runtime (outside model code a view is only borrowed)"

/-- A type term headed by an unsized declaration, read off syntax: an inductive type, or a
call of a type function whose body is one. The walk follows bodies of earlier definitions
only (a definition's types never mention it, and an accepted body that is itself a call calls
an earlier definition), so it ends; `seen` makes that an invariant checked here (a repeat is
an error, never "not unsized"). Lean cannot see that it ends (the bodies are looked up in the
state), so the walk is also bounded by the fuel left, and running out is exhaustion. -/
def unsizedTerm (T : Term) (seen : List String) : M Bool := do
  unsizedTermF (← fuelLeft) T seen
where
  unsizedTermF (fuel : Nat) (T : Term) (seen : List String) : M Bool := do
    let fuel' + 1 := fuel | exhausted "out of fuel"
    match T with
    | .tind n _ => pure (← lookupInd n).unsized
    | .val v => isUnsizedType v
    | .call (.const f) _ _ =>
      if seen.contains f then err s!"internal: the type functions unfolded from {f} call themselves"
      match (← lookupGlobal f).fn? with
      | some (.fix _ _ _ _ _ body) => unsizedTermF fuel' body (f :: seen)
      | _ => pure false
    | _ => pure false
  termination_by structural fuel

/-- K2/K3: a function is model code when it is `implemented by` native code, or a parameter
or its result has an unsized type by value (runtime code can never hold such a value). Read
from the declared types, syntactically (as D55 reads sorts): a type term headed by an unsized
declaration, directly or through type functions whose bodies are (`Slice(E, n)`). -/
def modelSignature (_hs : List Hint) (ds : List Term) (c : Term) : M Bool := do
  (c :: ds).anyM (unsizedTerm · [])

/-- Is `p` rooted in a closure's captured value? -/
def isCapture (p : Place) : M Bool := do
  match ← varPos p.root with
  | .bind f i => pure (← get).env[f]!.binds[i]!.cap
  | _ => pure false

/-- A match's scrutinee: a match inspects its place in place (no move). -/
def matchContent (p : Place) : M Value := do
  match ← content p with
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | v => pure v

/-- One step added to a place. -/
def stepPlace (q : Place) : Step → Place
  | .deref => .deref q | .fst => .fst q | .snd => .snd q | .field g => .field g q

mutual
/-- Where `loan_l` sits inside a value, as steps from it. -/
def loanPath (v : Value) (l : Nat) : M (Option (List Step)) := do
  match v with
  | .loan m => pure (if m == l then some [] else none)
  | .succ w => pure ((← loanPath w l).map (Step.fst :: ·))
  | .borrow _ w => pure ((← loanPath w l).map (Step.deref :: ·))
  | .ind t c _ _ fs =>
    let d ← lookupInd t
    let names := (d.ctors[c]?.map (·.2.map (·.1))).getD []
    loanPathFields t c names l 0 fs
  | _ => pure none
termination_by structural v

/-- The fields of constructor `c` of `t`, from field `i`: the first path to `loan_l`. -/
def loanPathFields (t : String) (c : Nat) (names : List String) (l i : Nat) :
    List Value → M (Option (List Step))
  | [] => pure none
  | w :: ws => do
    if let some ss ← loanPath w l then
      return some (Step.field ⟨t, c, i, names.getD i s!"f{i}"⟩ :: ss)
    loanPathFields t c names l (i + 1) ws
termination_by structural ws => ws
end

/-- A place `*r…` through a borrow variable `r` whose loan sits in an older binding of the
same frame: that binding's index and the steps from it to the place (the owner's move). -/
def throughLocalBorrow (f i : Nat) (p : Place) : M (Option (Nat × List Step)) := do
  let (_, ss) := p.steps
  let .deref :: rest := ss | return none
  let .borrow l _ := (← get).env[f]!.binds[i]!.val | return none
  let binds := (← get).env[f]!.binds
  for j in [0:i] do
    if let some path ← loanPath binds[j]!.val l then
      return some (j, path ++ rest)
  pure none

/-- D53: record an assignment, borrow or move of `p` by its root position (a stuck block's captures, `armMoves`). -/
def logEffect (p : Place) (kind : String) : M Unit := do
  if let .bind f i ← varPos p.root then
    -- D53: moves and assignments by place, from which a stuck block's effect on what it
    -- captures is read (`armMoves`); a step through a local borrow is also the owner's
    if kind == "moves" || kind == "assigns" then
      let isMove := kind == "moves"
      modify fun s => { s with placeLog := s.placeLog.push (f, i, p, isMove) }
      if let some (i', ss) ← throughLocalBorrow f i p then
        modify fun s => { s with placeLog := s.placeLog.push (f, i', ss.foldl stepPlace (Place.var 0), isMove) }

/-- A statement position (a type, `J`'s endpoints and motive, an erased call's parameter): it
runs on its own private copy of the state, which is thrown away (P2, D68). -/
def stmtCopy {α : Type} (x : M α) : M α := onCopy <| withErased x

/-- D64: the fields of the constructor value a place holds, as a constructor `g` names it:
through a loan (a place lent out
has its borrow's content). -/
def ctorFields (v : Value) (g : FieldRef) : M (Option (List Value)) := do
  ctorFieldsF (← fuelLeft) v g
where
  -- a loan's borrow may hold another loan: bounded by the fuel left, running out is exhaustion
  ctorFieldsF (fuel : Nat) (v : Value) (g : FieldRef) : M (Option (List Value)) := do
    let fuel' + 1 := fuel | exhausted "out of fuel"
    match v with
    | .ind t c _ _ fs => pure (if t == g.ty && c == g.ctor then some fs else none)
    | .loan l =>
      let env := (← get).env
      match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
      | some (c, _) => ctorFieldsF fuel' c g
      | none => pure none
    | _ => pure none
  termination_by structural fuel

/-- D64 [Open]: `p` is a data field whose declared type mentions earlier fields (its
assignment is a strong update). -/
def strongUpdate (p : Place) : M Bool := do
  let .field g _ := p | return false
  let some d := (← get).inds.find? (·.name == g.ty) | return false
  pure (d.fieldDependent g.ctor g.idx && !(← fieldIsProof g))

/-- D64: does a value hold a value of a dependent constructor (outside sealed programs and
closures, which carry their types)? -/
def hasDependent (v : Value) : M Bool := do
  match v with
  | .ind t c _ _ fs =>
    if (← lookupInd t).dependent c then return true
    anyList fs
  | .borrow _ w | .succ w => hasDependent w
  | _ => pure false
termination_by structural v
where
  /-- `vs.anyM hasDependent`. -/
  anyList : List Value → M Bool
    | [] => pure false
    | w :: ws => do if ← hasDependent w then return true else anyList ws
  termination_by structural ws => ws

/-- D44 (v1.9): a function type returning a borrow must take a borrow (no `'static`
borrows: a returned borrow derives from a borrow argument). -/
def borrowParamCheck (ds : List Term) (c : Term) : M Unit := do
  if (c matches .ref _) && !(ds.any (· matches .ref _)) then
    err s!"[D44] a function type returning a borrow ({c.pp []}) must have a borrow parameter"

/-- No borrows inside data (RULES §1), also through a parameter: `List(&Nat)` is not a type. -/
def noBorrowParam (n : String) (v : Value) : M Unit := do
  if v.typeHasRef then err s!"{n} at {v}: no borrows inside data (a parameter may not be a borrow type)"

/-- A statement position (an argument of a statement, a side of `Eq`): it runs on its own private
copy of the state, by the ordinary rules. An argument whose value holds a borrow cannot: the
borrow must be the real one (a copy's borrow would alias the place it borrows), so it runs in
place. -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 6): a value test, equal to a type test on every well-formed state: an argument is loan-free or a whole borrow (A.5 condition 5), and a borrow exactly when its type is a borrow type.
def stmtArgIf (b : Bool) (x : M (Value × Option Value)) : M (Value × Option Value) := do
  if !b then return ← x
  let r ← onCopy x
  if r.1.anyAtom (fun | .borrow .. | .loan _ => true | _ => false) then x else pure r

def fixOf (fv : Value) : M (List Value × Term) := do
  match fv with
  | .gfn n => match (← lookupGlobal n).fn? with
    | some t => pure ([], t)
    | none => err s!"{n} is not a function"
  | .clo cs t => pure (cs, t)
  | _ => err s!"{fv} is not a function"

/-- D53 (fuzz-port shape (c)): a returned borrow's content must be whole, as when a borrow
ends: a function may not hand back a borrow of a place it moved out of. -/
def wholeReturned (v : Value) : M Unit := do
  if let .borrow _ c := v then
    if c.hasHole then
      err s!"[D53] a returned borrow's content is partly moved out ({c})"

/-- D53 (fuzz-port P): a borrow passed at runtime to a call that closes off, or to an erased
call, must be whole. [Close] seals the borrowed place's content, which hides a hole, and an
erased call's writes vanish at runtime, so neither can make it whole before the borrow ends. -/
def wholeBorrowArgs (ws : Array Value) (what : String) : M Unit := do
  -- D68: a statement follows the runtime rules too
  for (w, i) in ws.toList.zipIdx do
    if let .borrow _ u := w then
      if u.hasHole then
        err s!"[D53] argument {i + 1} of {what} is a borrow whose content is partly moved out ({u})"

/-- [Rec]: at a recursive call, a parameter position survives if its argument (the
content, through a borrow) is a strict subterm of that parameter's entry value as
refined so far. The recursive position is any position that survives every call.
Every enclosing function being checked is considered, so a recursive call inside a
nested closure is checked against the outer function's entry values (fix L3). -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 15): the entry value as refined so far; refinement only adds constructors, so a strict subterm found here is one at every instance.
def recCheck (fv : Value) (ws : Array Value) : M Unit := do
  let st ← get
  let mut frames := #[]
  for ctx in st.recStack do
    if ctx.fn == fv then
      let cands := ctx.cands
      let cands' ← cands.filterM fun j => do
        match ctx.entries[j]?.join, ws[j]? with
        | some σ, some w =>
          let u := match w with | .borrow _ u => u | u => u
          return (strictSubterms (← expandRefs st.refs (.abs σ))).contains u
        | _, _ => pure false
      -- fail at the offending call, before it is run (running it may not terminate)
      if cands.isEmpty then
        err s!"[Rec] {fv} calls itself but declares no decreasing parameter (`by x`)"
      if cands'.isEmpty then
        err s!"[Rec] at {fv}({", ".intercalate (ws.toList.map toString)}): the argument in the decreasing position is not a strict subterm of that parameter's entry value as refined so far"
      frames := frames.push { ctx with cands := cands' }
    else frames := frames.push ctx
  set { st with recStack := frames.toList }

/-- Finding G1: a neutral that a [Split] generalised stays generalised when normalisation
derives it again (it is a closed, deterministic computation, so every derivation of it
denotes the same value). Returns its refined value if it is one. -/
def canonNeutral (v : Value) : M Value := do
  match v with
  | .sealed _ => match (← get).neutrals.lookup v with
    | some σ => expandRefs (← get).refs (.abs σ)
    | none => pure v
  | _ => pure v

/-- Two steps name the same part: a pair's `.1`/`.2` are its constructor's fields `fst`/`snd`
(the surface writes both; a Nat's `.1`, its predecessor, is never a pair's field). -/
def stepEq : Step → Step → Bool
  | .fst, .field g | .field g, .fst => g.ty == "Pair" && g.ctor == 0 && g.idx == 0
  | .snd, .field g | .field g, .snd => g.ty == "Pair" && g.ctor == 0 && g.idx == 1
  | a, b => a == b

/-- Place `q` is a prefix of place `p` (both rooted in the same frame). -/
def placePrefix (q p : Place) : Bool :=
  let (i, qs) := q.steps
  let (j, ps) := p.steps
  i == j && qs.length ≤ ps.length && ((ps.take qs.length).zip qs).all fun (a, b) => stepEq a b

/-- The same place (up to `stepEq`). -/
def placeEq (q p : Place) : Bool :=
  q.steps.2.length == p.steps.2.length && placePrefix q p

/-- D53: what a run left moved out among the bindings `(f0, i < n0)`, from its log of moves
and assignments in order: a move adds its place, an assignment restores every moved place it
covers. Places are rooted at the frame index the bindings had when the run started. -/
def armMoves (log : Array (Nat × Nat × Place × Bool)) (f0 n0 : Nat) : M (List Place) := do
  let mut out : List Place := []
  for (f, i, p, isMove) in log do
    if f != f0 || i ≥ n0 then continue
    let q := p.steps.2.foldl stepPlace (Place.var (n0 - 1 - i))
    if isMove then
      unless out.any (placeEq · q) do out := out ++ [q]
    else
      out := out.filter fun m => !placePrefix q m
  pure out

/-- D61 `split`: the name of a sealed program's head call (the call [Seal] marks as the
head; one per sealed program), if it is a top-level function. -/
def sealedHead : Term → Option String
  | .call (.val (.gfn n)) _ true => some n
  | .call f as _ => sealedHead f <|> firstOf as
  | .letIn _ a b | .seq a b => sealedHead a <|> sealedHead b
  | .assign _ a => sealedHead a
  | _ => none
termination_by structural t => t
where
  /-- `ts.findSome? sealedHead`. -/
  firstOf : List Term → Option String
    | [] => none
    | t :: ts => sealedHead t <|> firstOf ts
  termination_by structural ts => ts

/-- D61: the sealed programs of a value, in pre-order, left to right. -/
def sealedIn (v : Value) : List Term :=
  match v with
  | .sealed t => t :: termVals t
  | .succ w | .borrow _ w | .tRef w => sealedIn w
  | .tEq A a b => sealedIn A ++ sealedIn a ++ sealedIn b
  | .clo cs _ | .tPi cs _ => valsIn cs
  | .ind _ _ _ ps fs => valsIn ps ++ valsIn fs
  | .tInd _ as => valsIn as
  | _ => []
termination_by structural v
where
  valsIn : List Value → List Term
    | [] => []
    | w :: ws => sealedIn w ++ valsIn ws
  termination_by structural ws => ws
  termVals : Term → List Term
    | .val w => sealedIn w
    | .call f as _ => termVals f ++ termsIn as
    | .letIn _ a b | .seq a b => termVals a ++ termVals b
    | .assign _ a => termVals a
    | .prim _ as => termsIn as
    | _ => []
  termination_by structural t => t
  termsIn : List Term → List Term
    | [] => []
    | t :: ts => termVals t ++ termsIn ts
  termination_by structural ts => ts

/-- One arm of a stuck block (`closeBlock`): `setup` puts the state in the arm's world and
returns what it did (a [Split] arm refines the scrutinee and returns the refinement; the
transported term of a closed-off `J` has nothing to set up), and `body`, given that, checks the
arm and returns its result and type. The block runs both itself, so that no block can be formed
without its arms having been checked to their return (the producer obligation, D76). -/
structure BlockArm where
  setup : M Value
  body : Value → M (Value × Value)

-- the machine is one `mutual` block, and compiling it (LCNF) outgrew the default heartbeats
set_option maxHeartbeats 1000000 in
mutual

-- ### Substitution and normal forms ([Seal], refinement, [End])

/-- Substitute `r` for the variable `x` (an abstract value `σ` or a loan) in a value.
Values are kept in normal form (RULES §3 [Seal]): a sealed program that changed is
re-normalised (inner ones first, since the traversal rebuilds bottom-up), and `Eq`
and `∧` are rebuilt with their smart constructors. -/
def substV (fuel : Nat) (x r : Value) (v : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !(v.anyAtom (· == x)) then return v
  if v == x then return r
  match v with
  | .abs _ | .loan _ => return (if v == x then r else v)
  | .succ w => return .succ (← substV fuel' x r w)
  | .borrow l w => return .borrow l (← substV fuel' x r w)
  | .clo cs t => return .clo (← cs.mapM (substV fuel' x r)) (← substT fuel' x r t)
  | .tPi cs t => return .tPi (← cs.mapM (substV fuel' x r)) (← substT fuel' x r t)
  | .sealed t => nfSealed fuel' (← substT fuel' x r t)
  | .tEq A a b => mkEqM fuel' (← substV fuel' x r A) (← substV fuel' x r a) (← substV fuel' x r b)
  | .tInd n as => return .tInd n (← as.mapM (substV fuel' x r))
  | .tRef A => return .tRef (← substV fuel' x r A)
  | .ind t c h ps fs => return .ind t c h (← ps.mapM (substV fuel' x r)) (← fs.mapM (substV fuel' x r))
  | _ => return v
termination_by structural fuel

def substT (fuel : Nat) (x r : Value) (t : Term) : M Term := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !(t.anyAtom (· == x)) then return t
  let go := substT fuel' x r
  match t with
  | .val v => return .val (← substV fuel' x r v)
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
termination_by structural fuel

/-- Substitute in every value of Ω; with `types`, also in the stored types, the types
of abstract values and the goal ([Split]: "applied to Ω, the goal and all stored
types"). -/
def substEnv (fuel : Nat) (x r : Value) (types : Bool) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for p in allPos (← get).env do
    setAt p (← substV fuel' x r (← getAt p))
    if types then
      if let .bind f i := p then
        if let some T := (← get).env[f]!.binds[i]!.ty then
          -- a type's sealed programs re-run as types: erased, reads copy (D53, fuzz-port RN)
          let T' ← withErased (substV fuel' x r T)
          modifyFrame f fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }
  if types then
    withErased do
      let tys := (← get).absTy
      let mut tys' := #[]
      for T in tys do tys' := tys'.push (← substV fuel' x r T)
      modify fun s => { s with absTy := tys' }
      if let some g := (← get).goal then
        let g' ← substV fuel' x r g
        modify fun s => { s with goal := some g' }
termination_by structural fuel

/-- [Seal] `nf(⌈t⌉)`: run `t` from the empty environment. Its head call is marked
(`Term.call _ _ true`) and is not eligible for [Close]; loans whose borrow is outside
the run are inert (they have no borrow in the run's Ω). If the run completes, the
result is its value; if it is stuck, `⌈t⌉` (its embedded values are already normal). -/
def nfSealed (fuel : Nat) (t : Term) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let saved ← get
  -- bounded like calls, so that a normalisation loop (breaker-fresh-v16 X5 without D39)
  -- is an error rather than a stack overflow
  if saved.depth ≥ 2000 then exhausted "normalisation depth exceeded (a sealed program that re-closes itself)"
  modify fun s => { s with env := #[{}], depth := s.depth + 1 }
  -- D53: a sealed program re-runs with runtime semantics (moves, ⊥ checks); only its final
  -- read of a cell (`peek`, closeCall's `K`) is an observation, and copies
  -- [Seal-stuck]: a stuck run leaves `⌈t⌉`; an error or exhaustion is rethrown ([Seal-err])
  let r ← catchStuck (do let (v, _) ← eval fuel' false t; pure (some v)) fun _ => pure none
  restoreKeep saved
  match r with
  | some v => pure v
  | none => canonNeutral (.sealed t)
termination_by structural fuel

-- ### Borrows: [End], [Access], [Read], [Borrow], [Assign], [Drop]

/-- [End ℓ]: replace `borrow_ℓ v` by `⊥` and substitute `v` for every `loan_ℓ`. A loan
whose borrow is not in Ω is inert: nothing happens. -/
def endBorrow (fuel : Nat) (l : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
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
          repackCheck fuel' "a borrow of it ends" c A
      -- D68: an observation reads what a side consumed as `⊥` (its equation is stuck, `mkEqM`)
      if c.hasHole && !(← get).observing then
        -- the temporary of a dereferenced call (`*f(ā)`, a surface desugaring) is named `⋄*f(…)`
        match p with
        | .bind f i =>
          let x := env[f]!.binds[i]!.hint.name
          if x.startsWith "⋄*" then
            let call := (x.drop 2).toString
            err s!"[D53] reading *{call} moves its content out through the borrow {call} returns, which then ends with it moved out ({c}): copy it with clone(*{call}), or write it back first"
        | _ => pure ()
        err s!"[D53] a borrow ends while its content is partly moved out ({c})"
      setAt p rest
      substEnv fuel' (.loan l) c false
termination_by structural fuel

/-- D73 [Repack] with what is lent unknown: a live loan inside a value stands for whatever
its borrow may still write, a fresh abstract value of the lent content's type, not the
content the borrow holds now ([Open]'s reading of a lent part, at whole-again points). -/
def lentUnknown (fuel : Nat) (v : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match v with
  | .loan l =>
    let env := (← get).env
    match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
    | some (c, _) =>
      match ← valType? fuel' c with
      | some T => pure (.abs (← freshAbs T))
      | none => pure v
    | none => pure v
  | .succ w => pure (.succ (← lentUnknown fuel' w))
  | .ind t c h ps fs => pure (.ind t c h ps (← fs.mapM (lentUnknown fuel')))
  | _ => pure v
termination_by structural fuel

/-- D64 [Repack]: at a whole-again point, a value holding values of dependent types must be
of its type `T` by their telescopes again (a borrow's content, for a borrow of `&A`). D73: a
part that is still lent is checked as an unknown of its type (`lentUnknown`), since its
borrow may still write any such value there. -/
def repackCheck (fuel : Nat) (what : String) (v : Value) (T : Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (v, T) := match v, T with
    | .borrow _ c, .tRef A => (c, A)
    | _, _ => (v, T)
  if !(← hasDependent v) then return
  let v ← lentUnknown fuel' v
  fire .Repack fun _ => s!"{what}: {v} : {T}"
  if let some m ← packedErr fuel' v T then err s!"[Repack] {what}, but it is open: {m}"
termination_by structural fuel

/-- D64 [Repack] at a whole use of the place `p` (of type `T`): read, moved, borrowed, passed
or captured whole. A place moved out or ended is left to the machine's own error. -/
def repackAt (fuel : Nat) (p : Place) (T : Value) (what : String) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some v ← content? p | return
  if v matches .bot then return
  repackCheck fuel' s!"{← ppPlace p} is {what}" v T
termination_by structural fuel

/-- [Return], the producer obligation's one check (D76). A checked body returns, so what it
hands back must be whole: each place it holds by borrow, whose borrow ends here, and its result,
each of its type by the telescopes of the dependent constructors inside it, a part still lent
being unknown (`repackCheck`, D73). The generic path treats every sealed program as whole, and a
sealed program is a call ([Close]) of a function value; every function value a checked program
can call is either its caller's abstract value, or formed by a check that ends here: [Def] and
[Fix] (`checkFix`) at their body's return, whose borrow parameters are real borrows that the
frame's pop then ends ([End], which repacks them too), and a stuck block (`closeBlock`), an
anonymous function of the places it captures, at the end of each arm, where its borrow
parameters are the places it takes by `&`, given here as `lent`. -/
def bodyReturns (fuel : Nat) (what : String) (v T : Value) (lent : List Place) (lentWhat : String) :
    M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for q in lent do
    let Tq ← placeType fuel' q
    repackAt fuel' q Tq lentWhat
  repackCheck fuel' what v T
termination_by structural fuel

/-- End every borrow in Ω (for observations, §4). -/
def endAll (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let env := (← get).env
  match (allPos env).findSome? (fun p => firstBorrowLabel (valAt env p)) with
  | some l => endBorrow fuel' l; endAll fuel'
  | none => pure ()
termination_by structural fuel

/-- [Access], path part: end every borrow whose loan is on the path to `p`. -/
def accessPath (fuel : Nat) (p : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (i, ss) := p.steps
  let env := (← get).env
  match firstLiveLoanOnPath env (valAt env (← varPos i)) ss with
  | some l => endBorrow fuel' l; accessPath fuel' p
  | none => pure ()
termination_by structural fuel

/-- [Access], content part: end every borrow whose loan occurs inside `content(p)`. -/
def accessInside (fuel : Nat) (p : Place) (owned : Bool := false) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let v ← content p
  -- D67: before an assignment, only the part of the content the place owns (`owned`)
  let ls := (if owned then liveOwnedLoansIn else liveLoansIn) (← get).env v
  unless ls.isEmpty do
    fire .Access fun _ => s!"loans {ls} inside {v}{if owned then " (the part the place owns: before an assignment, D67)" else ""}"
  match ls with
  | l :: _ => endBorrow fuel' l; accessInside fuel' p owned
  | [] => pure ()
termination_by structural fuel

/-- [Access] for matching (v1.5, D29): a loan anywhere inside a neutral at the head of
`content(p)` counts as being at the head (its position inside the neutral is unknown),
so its borrow ends. -/
def accessNeutralHead (fuel : Nat) (p : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let v ← content p
  match v with
  | .sealed _ | .abs _ =>
    match liveLoansIn (← get).env v with
    | l :: _ => endBorrow fuel' l; accessNeutralHead fuel' p
    | [] => pure ()
  | _ => pure ()
termination_by structural fuel

/-- [Read]: reading a place moves its content out (`p ↦ ⊥`), in any term: a statement runs on
its own private copy, so its moves are undone with the copy (one mental model, D68). Content
is copied when its type is a copy type, and by `clone`. A place partly moved out cannot be read (D53 (h)). -/
def readPlace (fuel : Nat) (p : Place) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  accessPath fuel' p; accessInside fuel' p
  let v ← content p
  unsizedCheck p v "read"
  let erased := (← get).erasedDepth > 0
  let inPlace := (← get).inPlace
  if inPlace then modify fun s => { s with inPlace := false }
  match v with
  | .bot =>
    if let .field g _ := p then
      if (← lookupInd g.ty).dependent g.ctor && (← fieldIsProof g) then
        err s!"[Open] {← ppPlace p} is a proof field invalidated by a write to a field its type mentions: assign it a new proof first"
    err s!"[Read] {← ppPlace p} was moved out or its borrow ended (reading ⊥)"
  | .borrow _ _ => logEffect p "moves"; setPlace p .bot; pure v
  | _ =>
    if v == .proof then return v
    if (← get).copying then return v
    -- read in place: not consumed, but it must be there (D53: a call's head, the Fn rule;
    -- a stuck block's read-only capture, as the match inspects its place)
    if inPlace then
      if v.hasHole then err s!"[Read] {← ppPlace p} was partly moved out (D53)"
      return v
    -- a copy-type value is read whole whatever it holds (a proposition whose stuck equation
    -- mentions a moved place, D68)
    if ← copyRead fuel' p v then return v
    if v.hasHole then err s!"[Read] {← ppPlace p} was partly moved out (D53)"
    if !erased && (← isCapture p) then
      err s!"[D53] a closure's body moves a captured value out ({← ppPlace p}); a closure may run again: clone it"
    logEffect p "moves"
    setPlace p .bot
    pure v
termination_by structural fuel

/-- D53: reading `p` (holding `v`) copies: its type is a copy type, or it holds a function
whose captures are copies (the Fn rule). -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 16): copy-ness of the stored type; an abstract or neutral type is never a copy type, so the generic call moves at least what an instance moves.
def copyRead (fuel : Nat) (p : Place) (v : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- an untyped run (a called body) may not know a pattern variable's type: the value's own
  -- type, read off its constructor, is its type
  -- a type that cannot be read is not known to be a copy type (`isCopyType`): the read moves
  let T? ← match ← placeType? fuel' p with
    | some T => pure (some T)
    | none => valType? fuel' v
  match T? with
  -- D68: copy-ness is the type's, never the value's: a Π type is not a copy type, so reading a
  -- Π-typed place moves it, whatever function it holds
  | some T => isCopyType fuel' T
  | none => pure false
termination_by structural fuel

/-- [Borrow] `&p ⇓ borrow_ℓ v` with `p ↦ loan_ℓ`. -/
def borrowPlace (fuel : Nat) (p : Place) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  accessPath fuel' p; accessInside fuel' p
  let v ← content p
  match v with
  | .bot => err s!"[Borrow] {← ppPlace p} was moved out (borrowing ⊥)"
  | .borrow _ _ => err "[Borrow] a borrow of a borrow (&&T is outside the core)"
  | _ =>
    if v.hasHole then
      err s!"[Borrow] {← ppPlace p} was partly moved out (D53)"
    logEffect p "borrows"
    let l ← freshLoan
    setPlace p (.loan l)
    pure (.borrow l v)
termination_by structural fuel

/-- [Assign] with the value already computed: drop the old content, store the new. -/
def assignPlace (fuel : Nat) (p : Place) (v : Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pushTemp v
  -- D67: a loan behind a borrow the old content holds is not ended: [Drop] of the old borrow
  -- ([End]) carries it back to its owner, where it stays live (reborrow-and-replace,
  -- `x := &(*x).f`). Loans in the owned part, neutrals there included, still end
  accessPath fuel' p; accessInside fuel' p true
  let old ← content p
  unsizedCheck p old "assigned"
  match old with
  | .borrow l _ => endBorrow fuel' l
  | _ =>
    if !(liveLoansIn (← get).env old).isEmpty then
      err s!"[Drop] the old content of {← ppPlace p} is overwritten while borrowed"
  let v' ← popTemp
  logEffect p "assigns"
  setPlace p v'
termination_by structural fuel

/-- [Drop] the most recent binding of the top frame: a borrow ends. An owned value holding
a live loan ends that loan's borrower if the borrower is held in a binding (D65 amended: the
non-lexical-lifetime reading, the borrower is not used again), and is an error if the borrower
is a value in flight (a block or a function may not return a borrow of its own local). -/
def dropTopBind (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f ← topIdx
  let some b := (← get).env[f]!.binds.back? | err "internal: no binding to drop"
  match b.val with
  | .borrow l _ => endBorrow fuel' l
  | _ => endLoansOfTopBind fuel' f
  modifyFrame f fun fr => { fr with binds := fr.binds.pop }
termination_by structural fuel

/-- D65 amended: end the borrowers of the live loans in the top frame's last binding, repeating
as [Access] does (ending one brings its content's loans in); a borrower in flight is an error. -/
def endLoansOfTopBind (fuel : Nat) (f : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some b := (← get).env[f]!.binds.back? | pure ()
  match liveLoansIn (← get).env b.val with
  | l :: _ =>
    match findBorrow (← get).env l with
    | some (.temp _ _) => err s!"[Drop] {b.hint.name} dies while a value in flight borrows it"
    | _ => endBorrow fuel' l; endLoansOfTopBind fuel' f
  | [] => pure ()
termination_by structural fuel

/-- [Drop] a discarded value (`t; u`). -/
def dropValue (fuel : Nat) (v : Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pushTemp v
  match v with
  | .borrow l _ => endBorrow fuel' l
  | _ => endLoansOfTopTemp fuel'
  discard popTemp
termination_by structural fuel

/-- D65 amended, for a discarded value (the top temporary): end the borrowers of its live
loans, repeating; a borrower in flight is an error. -/
def endLoansOfTopTemp (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f ← topIdx
  let some v := (← get).env[f]!.temps.back? | pure ()
  match liveLoansIn (← get).env v with
  | l :: _ =>
    match findBorrow (← get).env l with
    | some (.temp _ _) => err "[Drop] a discarded value dies while a value in flight borrows it"
    | _ => endBorrow fuel' l; endLoansOfTopTemp fuel'
  | [] => pure ()
termination_by structural fuel

/-- Pop the top frame, dropping its bindings (most recent first). -/
def popFrame (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f ← topIdx
  let n := (← get).env[f]!.binds.size
  for _ in [0:n] do dropTopBind fuel'
  discard popFrameRaw
termination_by structural fuel

-- ### Types

/-- The type of a place, read off the stored types (RULES §5; e1 F9). A total query: `none`
when the type cannot be read (an untyped binding whose value has no readable type, `valType?`),
an error when the place is ill-formed at the type it has. -/
def placeType? (fuel : Nat) (p : Place) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match p with
  | .var i =>
    let pos ← varPos i
    match ← tyAt pos with
    | some T => pure (some T)
    | none => valType? fuel' (← getAt pos)
  | .deref q => match ← placeType? fuel' q with
    | none => pure none
    | some (.tRef T) => pure (some T)
    | some T =>
      let q' ← ppPlace q
      -- the temporary of a dereferenced call (`*f(ā)`, a surface desugaring) is named `⋄*f(…)`
      if q'.startsWith "⋄*" then
        let call := (q'.drop 2).toString
        err s!"*{call}: {call} does not return a borrow (type {T}), so *{call} is not a place"
      err s!"*{q'}: not a borrow (type {T})"
  | .fst q => match ← placeType? fuel' q with
    | none => pure none
    | some .tNat => pure (some .tNat)
    | some (.tInd "Pair" [A, _]) => pure (some A)           -- field 1 of the library's Pair (D52)
    | some T => err s!"{← ppPlace q}.1: no sub-place at type {T}"
  | .snd q => match ← placeType? fuel' q with
    | none => pure none
    | some (.tInd "Pair" [_, B]) => pure (some B)
    | some T => err s!"{← ppPlace q}.2: no sub-place at type {T}"
  | .field g q => match ← placeType? fuel' q with
    | none => pure none
    | some (.tInd n ps) =>
      -- the place names its constructor (v2.0), so a proof's field has a type too
      if n != g.ty then err s!"{← ppPlace q}.{g.name}: a field of {g.ty}, at type {n}"
      let d ← lookupInd n
      if d.dependent g.ctor then return some (← depFieldType fuel' d ps g q)
      match (← fieldTypes fuel' d ps g.ctor)[g.idx]? with
      | some (_, T) => pure (some T)
      | none => err s!"{← ppPlace q}.{g.name}: no such field"
    | some T => err s!"{← ppPlace q}.{g.name}: no field at type {T}"
termination_by structural fuel

/-- The type of a place, which must be readable (`placeType?`). -/
def placeType (fuel : Nat) (p : Place) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← placeType? fuel' p with
  | some T => pure T
  | none => err s!"cannot infer the type of the place {← ppPlace p}"
termination_by structural fuel

/-- D64, rule 2 and [Open]: the type of field `g` of the value at `q`, of the dependent
constructor `g.ctor` of `d` at parameters `ps`. Its type by the telescope is computed from
the earlier fields' current contents. A field whose declared type mentions no earlier field
has that type. Any other field has it while its content does (the value is packed);
otherwise the value is *open*, and the field is typed by its content's own type (what was
written into it, a stored type), until the value is repacked. -/
def depFieldType (fuel : Nat) (d : IndDecl) (ps : List Value) (g : FieldRef) (q : Place) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !d.fieldDependent g.ctor g.idx then
    match ← fieldTypeAt fuel' d ((ps.map some).toArray) g.ctor g.idx [] with
    | some T => return T
    | none => err s!"{← ppPlace q}.{g.name}: no such field"
  let cv ← content q
  let some fs ← ctorFields cv g
    | err s!"{← ppPlace q}.{g.name}: its type depends on the earlier fields of {g.ty}, but {← ppPlace q} holds {cv}, not a value of its constructor (match on it first)"
  -- D64: a field's type from the earlier fields' contents
  let some (_, T) := (← fieldTypesOf fuel' d ps g.ctor fs (some (g.idx + 1)))[g.idx]?
    | err s!"{← ppPlace q}.{g.name}: no such field"
  fire .Field fun _ => s!"{g.name}: {T}, from the earlier fields' contents"
  if !d.fieldDependent g.ctor g.idx then return T
  let c := fs.getD g.idx .bot
  if c == .bot || c == .proof then return T
  if (← packedErr fuel' c T).isNone then return T
  -- a content with no readable type of its own (a proof, an inert loan) keeps the field's type
  let S := (← valType? fuel' c).getD T
  fire .Open fun _ => s!"{g.name} is open: typed by its content, {S}, not {T}"
  pure S
termination_by structural fuel

/-- D64 [Repack]: why `v` is not a value of `T` by the telescopes of the dependent
constructors inside it, or `none`. A constructor value is checked field by field against its
field types, computed from its own earlier fields and `T`'s parameters; a leaf by its own type
(an abstract value's stored type, a sealed program's, a proof against a proposition). A hole
(`⊥`) is not packed. A constructor value with no dependent constructor inside whose
type is `T` needs no walk. -/
def packedErr (fuel : Nat) (v : Value) (T : Value) : M (Option String) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match v with
  | .bot => pure (some s!"it holds {v} (moved out, or a proof invalidated by a write to a field its type mentions)")
  | .proof => pure (if ← isPropV fuel' T then none else some s!"a proof where {T} is expected")
  | .ind t c _ ps fs =>
    if !(← hasDependent v) && (← convVal fuel' v T) then return none
    let d ← lookupInd t
    -- `T` must be `t` applied to parameters: a value of another inductive, or one under a stuck
    -- type, is not of `T` (never checked against its own type instead: `O : One` is not a
    -- `Fin1(0)`, nor a `⌈Fin1(σ)⌉`, fuzz-port's --dep family)
    let some as := (match T with
        | .tInd n as => if n == t then some as else none
        | _ => none)
      | return some s!"{v} is not of type {T}"
    if !ps.isEmpty && !(← convList fuel' ps as) then return some s!"{v} is not of type {T}"
    let tel ← fieldTypesOf fuel' d as c fs
    let cn := (d.ctors[c]!).1
    for (((f, Tf), fv), j) in (tel.zip fs).zipIdx do
      if let some m ← packedErr fuel' fv Tf then
        let own := (← valType? fuel' fv).getD .bot
        -- name the field, and show both types: what it holds, and its type from the earlier fields
        return some (match fv with
          | .bot => s!"field {f} of {cn}: {m}"
          | _ =>
            if m.startsWith "field " || m.startsWith "in field " then s!"in field {f} of {cn}, {m}"
            else if d.fieldDependent c j then
              s!"field {f} of {cn} holds a value of type {own}, but its type from the earlier fields is {Tf}"
            else s!"field {f} of {cn}: {m}")
    pure none
  | .abs σ =>
    let A ← absType σ
    pure (if ← conv fuel' A T then none else some s!"{v} : {A}, not {T}")
  | _ => pure (if ← convVal fuel' v T then none else some s!"{v} is not of type {T}")
termination_by structural fuel

/-- The type of a leaf value converts to `T` (a value whose type cannot be read does not). -/
def convVal (fuel : Nat) (v : Value) (T : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← valType? fuel' v with
  | some S => conv fuel' S T
  | none => pure false
termination_by structural fuel

/-- The type of a value, for untyped bindings (captured values) and embedded values. A total
query: `none` for a value that has no readable type of its own (`⊥`, `⋆`, an inert loan, a
constructor value whose parameters no field determines, a sealed program its typing run gives
no type); an error only from a step that fails (an undeclared name, a failing typing run). -/
def valType? (fuel : Nat) (v : Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match v with
  | .zero | .succ _ => pure (some .tNat)
  | .unit => pure (some .tUnit)
  | .abs σ => some <$> absType σ
  | .gfn n => pure (some (← lookupGlobal n).ty)
  | .clo cs (.fix _ hs ds c _ _) => pure (some (.tPi cs (.pi hs ds c)))
  | .borrow _ w => pure ((← valType? fuel' w).map .tRef)
  | .ind t c _ ps fs => if ps.isEmpty then indValType? fuel' t c fs else pure (some (.tInd t ps))   -- D49 (4)
  | .tNat | .tUnit | .tEq .. | .tRef _ | .tPi .. | .sort _ | .tInd .. =>
    pure (some (.sort (← sortOf fuel' v)))
  | .sealed t =>
    sealedType? fuel' t
  | .loan l =>
    -- a live loan's value is its borrow's content: a place lent out has that content's type
    let env := (← get).env
    match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
    | some (c, _) => valType? fuel' c
    | none => pure none
  | _ => pure none
termination_by structural fuel

/-- The type of a value, which must be readable (`valType?`). -/
def valType (fuel : Nat) (v : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← valType? fuel' v with
  | some T => pure T
  | none => err s!"cannot infer the type of the value {v}"
termination_by structural fuel

/-- The type of a sealed program (neutral data, e.g. a captured one): its term typed as
an ordinary term on a private copy, from the empty environment. Its head call is not
marked, so a stuck body closes off; its [Call-type] is what gives the type. -/
def sealedType? (fuel : Nat) (t : Term) : M (Option Value) := onCopy do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  modify fun s => { s with env := #[{}], recStack := [], goal := none }
  let (_, T) ← eval fuel' true t.unHead
  pure T
termination_by structural fuel

-- ### Inductive declarations (v2.0: D45–D47)

/-- The field types of constructor `c` of `d` at the parameters `ps` (D46), as a telescope
(D64, [Ind]): the declared field type terms are evaluated in order, in a frame binding the
parameters and the fields, field `j` bound to `val j Tⱼ` once its type `Tⱼ` is known (its
content, or a fresh generic value). A field not yet bound is `⊥`, which a well-formed
telescope never reads (a field type mentions only earlier fields). Only the first `upto`
fields are computed. Returns each field's name, type and bound value. The frame is pushed on
the real state, not a copy, so that the values `val` creates (fresh σ) survive. -/
def fieldTele (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (val : Nat → Value → M Value)
    (upto : Option Nat := none) : M (List (String × Value × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some (_, fields) := d.ctors[c]? | err s!"{d.name} has no constructor {c}"
  if ps.length != d.params.length then
    err s!"{d.name} takes {d.params.length} parameters, given {ps.length}"
  let fields := match upto with | some n => fields.take n | none => fields
  let k := (d.ctors[c]!).2.length
  pushFrame
  let r ← onFail (do
      -- the fields first (`var np …`), then the parameters (`var 0 …`), as resolved
      for i in [0:k] do pushBind ⟨((d.ctors[c]!).2[i]!).1⟩ none .bot
      for ((h, PT), v) in d.params.zip ps do
        let pd' ← withLive true (typeDecl fuel' false [] [] PT)
        pushBind h none v pd'.isProof pd'
      let top ← topIdx
      let mut out := #[]
      for ((f, FT), j) in fields.zipIdx do
        let T ← evalType fuel' FT
        let v ← val j T
        out := out.push (f, T, v)
        let p ← fieldTermIsProp d FT
        modifyFrame top fun fr => { fr with binds := fr.binds.modify j fun b =>
          { b with val := v, ty := some T, proof := p, decl := if p then .prop else .other } }
      pure out.toList) (discard popFrameRaw)
  discard popFrameRaw
  pure r
termination_by structural fuel

/-- The field types of constructor `c` at the parameters `ps`, for a constructor with no
dependent field (D46); a dependent one needs its fields' values (`fieldTypesOf`). -/
def fieldTypes (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) : M (List (String × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if d.dependent c then err s!"internal: the field types of {d.name}'s constructor {c} depend on its fields"
  pure ((← fieldTele fuel' d ps c (fun _ _ => pure .bot)).map fun (f, T, _) => (f, T))
termination_by structural fuel

/-- D64: the field types of constructor `c` at the parameters `ps` and the field values
`fs` (rule 2: a field's type is computed from the earlier fields' contents). -/
def fieldTypesOf (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (fs : List Value)
    (upto : Option Nat := none) : M (List (String × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pure ((← fieldTele fuel' d ps c (fun j _ => pure (fs.getD j .bot)) upto).map fun (f, T, _) => (f, T))
termination_by structural fuel

/-- D64: fresh generic values for the fields of constructor `c`, each of its type computed
from the earlier ones ([Ind] and [Split]: `σ := C(σ₁, σ₂)` with `σ₂ : T₂[σ₁]`); a proof
field is `⋆`. Returns each field's name, type and value. -/
def fieldsGeneric (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) :
    M (List (String × Value × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  fieldTele fuel' d ps c fun _ T => genericValue fuel' T
termination_by structural fuel

/-- D53: a copy type, read off a type; a type not fully known is not one: `Unit`, a sort
(types are erased), a proposition (its values are `⋆`), an inductive declared `copy`
(`Word`), and an inductive in `Type₀` whose fields do not mention it and are copy types at
the parameters (`Bool`, a pair of copy types). Not `Nat`, not a recursive type, not a
function type (D68: copy-ness is the type's, never the value's), not a neutral. -/
def isCopyType (fuel : Nat) (T : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if ← isPropV fuel' T then return true   -- a proposition
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
      for (_, FT) in ← fieldTypes fuel' d args i do
        unless ← isCopyType fuel' FT do return false
    pure true
  | _ => pure false
termination_by structural fuel

/-- One declared field type, field `i` of constructor `c`, at partially known parameters and
the values of the fields before it (for a hint; unknown parameters and fields are bound to
`⊥`, which a field type not mentioning them never reads). -/
def fieldTypeAt (fuel : Nat) (d : IndDecl) (sol : Array (Option Value)) (c i : Nat) (earlier : List Value) :
    M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let np := d.params.length
  let some (_, fields) := d.ctors[c]? | return none
  let some (_, FT) := fields[i]? | return none
  let k := fields.length
  unless FT.freeVars.all fun j => (j < np && (sol[np - 1 - j]!).isSome) ||
      (np ≤ j && j < np + k && np + k - 1 - j < earlier.length) do return none
  onCopy do
    pushFrame
    for jj in [0:k] do pushBind ⟨(fields[jj]!).1⟩ none (earlier.getD jj .bot)
    for ((h, PT), v) in d.params.zip sol.toList do
      pushBind h none (v.getD .bot) false (← withLive true (typeDecl fuel' false [] [] PT))
    some <$> evalType fuel' FT
termination_by structural fuel

/-- The type of a constructor value (for untyped bindings): its parameters are inferred
from its fields' types; a parameter no field determines (the `A` of `Nil`) is unknown. -/
def indValType? (fuel : Nat) (t : String) (c : Nat) (fs : List Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let d ← lookupInd t
  if d.params.isEmpty then return some (.tInd t [])
  let some (_, fields) := d.ctors[c]? | err s!"{t} has no constructor {c}"
  let mut sol := Array.replicate d.params.length none
  for (v, (_, FT)) in fs.zip fields do
    let some T ← valType? fuel' v | return none
    sol := unifyParams d.params.length FT T sol
  pure ((sol.toList.mapM id).map fun ps => .tInd t ps)
termination_by structural fuel

/-- D49 (3): in an arm of a match on a proof, a data field is bound to a fresh abstract
value (as [Def] binds a parameter) and a proof field stays a place holding `⋆`. The arm
becomes `let g = σ; …; arm'`, with the field's place (and places under it) replaced by
the local and every other free place shifted past the new bindings. -/
def bindDataFields (fuel : Nat) (p : Place) (d : IndDecl) (ps : List Value) (c : Nat) (arm : Term) : M Term := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some (_, fields) := d.ctors[c]? | return arm
  -- D64: a dependent constructor's fields are all bound, in order, each at its type from the
  -- earlier ones: data to fresh values, proofs to `⋆` at their types (whose type a later
  -- field's may read)
  let dep := d.dependent c
  let fts ← if dep then fieldsGeneric fuel' d ps c
    else pure ((← fieldTypes fuel' d ps c).map fun (f, T) => (f, T, Value.bot))
  let mut datas : Array (Nat × String × Value × Term) := #[]
  for (((fname, FT), (_, T, v)), i) in (fields.zip fts).zipIdx do
    if ← fieldTermIsProp d FT then
      if dep then datas := datas.push (i, fname, T, .ascribe (.val .proof) (.val T))
    else
      let g ← if dep then pure v else genericValue fuel' T
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
termination_by structural fuel

/-- [T-Pi]: a Π-type's parameter types and codomain are types, each evaluated with the earlier
parameters bound to generic values, on a private copy; its sort is the largest of theirs, or
`Prop` when the codomain is a proposition (impredicativity). This is typing, so it runs the
parameter types (and so checks them: `&Type` is not a type, D66); the decisions read the
sort off the terms instead (`Decide.sortOf`), and `evalCore` asserts the two agree. -/
def piSort (fuel : Nat) (T : Value) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .tPi cs (.pi hs ds c) := T | err s!"{T} is not a Π-type"
  onCopy do
    pushFrame
    pushCaps fuel' cs
    let (pds, _) ← paramDecls fuel' cs hs ds c
    let mut l := 0
    for ((d, h), pd) in (ds.zip hs).zip pds do
      let A ← evalType fuel' d
      l := max l (← sortOf fuel' A)
      let gv ← genericValue fuel' A
      let pd' ← refineDecl fuel' pd (some A) gv
      pushBind h (some A) gv pd'.isProof pd'
    let lb ← sortOf fuel' (← evalType fuel' c)
    pure (if lb == 0 then 0 else max l lb)
termination_by structural fuel

/-- Evaluate a type (P2: once, against the current Ω, on a private copy). -/
def evalType (fuel : Nat) (t : Term) : M Value := stmtCopy do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (v, T) ← eval fuel' true t
  match T with
  | some (.sort _) => pure v
  | some T => err s!"{t.pp []} is not a type (it has type {T})"
  | none => pure v
termination_by structural fuel

/-- Close a `pi`/`fix` term over the current values of its free variables (P2: a
Π-type is a closure over formation-time values, like a λ). Captured values are copied;
closures capture no borrows (RULES §1). -/
def capture (fuel : Nat) (t : Term) : M (List Value × Term) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let fvs := (t.freeVars.toArray.qsort (· > ·)).toList   -- oldest binding first
  let m := fvs.length
  let mut vals := #[]
  let top0 := (← get).env.back!
  for o in fvs do
    -- [Fix] captures no borrow, a stuck block's borrow parameter included (D63, rule-audit
    -- item 7)
    let b0 := top0.binds[top0.binds.size - 1 - o]!
    let p := Place.var o
    accessPath fuel' p; accessInside fuel' p
    let v ← content p
    match v with
    | .borrow _ _ =>
      let n := ((← get).env.back!.binds[(← get).env.back!.binds.size - 1 - o]!).hint.name
      err s!"a closure or Π-type captures the borrow {n} (closures capture no borrows, RULES §1)"
    | .bot => err "a closure or Π-type captures a moved place"
    | _ =>
      -- D64 [Repack]: a closure or Π-type captures the value whole
      if (← get).typing then
        if let some T := b0.ty then
          repackCheck fuel' s!"a closure or Π-type captures {b0.hint.name}" v T
      vals := vals.push v
      -- D53: a runtime closure moves the variables it captures whose types are not copies
      if !(v matches .proof) then
        if v.hasHole then err "[D53] a closure captures a place that was partly moved out"
        unless ← copyRead fuel' p v do
          if (← get).erasedDepth == 0 && (← isCapture p) then
            err s!"[D53] a closure's body moves a captured value ({← ppPlace p}) into a closure; clone it"
          logEffect p "moves"
          setPlace p .bot
  let idx (o : Nat) : Nat := (fvs.findIdx? (· == o)).getD 0
  let mut t' := t.mapFree (fun c o => .var (c + m - 1 - idx o)) 0
  -- a captured proof keeps its type: its reads are inlined as `(⋆ : T)` (a proof's value
  -- is ⋆, so the type is all there is to record). "A proof" is the binding's declared
  -- flag, never its value (finding P3: `g(0)` may be ⋆ at an instance only)
  let top := (← get).env.back!
  for (o, k) in fvs.zipIdx do
    let b := top.binds[top.binds.size - 1 - o]!
    if b.proof then
      if let some T := b.ty then
        t' := t'.inlineReads (m - 1 - k) (.ascribe (.val .proof) (.val T)) 0
  relocate t t'     -- the editor: the rebuilt body keeps its source ranges
  pure (vals.toList, t')
termination_by structural fuel

-- ### Conversion (P1, v1.5 D30)

/-- Conversion: same normal form, where the normal form of a function value is the
observation of its generic call (its result and the final contents of the generic
owned places) plus its captured values (D30). Structural everywhere else. -/
def conv (fuel : Nat) (v w : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if v == w then return true
  -- D50: the unit laws And(True, P) ≡ P ≡ And(P, True) are conversion rules
  let v := unitTop v
  let w := unitTop w
  if v == w then return true
  match v, w with
  | .succ a, .succ b | .tRef a, .tRef b => conv fuel' a b
  | .tInd n as, .tInd m bs => pure (n == m && (← convList fuel' as bs))
  | .tEq A a b, .tEq B c d => pure ((← conv fuel' A B) && (← conv fuel' a c) && (← conv fuel' b d))
  | .borrow l a, .borrow m b => pure (l == m && (← conv fuel' a b))
  | .ind t c _ _ fs, .ind u d _ _ gs => pure (t == u && c == d && (← convList fuel' fs gs))
  | .sealed t, .sealed u => convT fuel' t u
  | .tPi cs t, .tPi ds u =>
    if (← convList fuel' cs ds) && (← convT fuel' t u) then return true   -- same captures and code
    convPi fuel' v w
  | f, g =>
    let isFn : Value → Bool := fun | .gfn _ | .clo _ _ => true | _ => false
    if isFn f && isFn g then convFn fuel' f g else pure false
termination_by structural fuel

def convList (fuel : Nat) : List Value → List Value → M Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    let fuel' + 1 := fuel | exhausted "out of fuel"
    pure ((← conv fuel' a b) && (← convList fuel' as bs))
  | _, _ => pure false
termination_by structural fuel

def convTList (fuel : Nat) : List Term → List Term → M Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    let fuel' + 1 := fuel | exhausted "out of fuel"
    pure ((← convT fuel' a b) && (← convTList fuel' as bs))
  | _, _ => pure false
termination_by structural fuel

/-- D48 (3): two Π-types are convertible when, their binders instantiated with the same
fresh generic values (a fresh owned place behind each borrow parameter, `⋆` for a proof,
as at [Def]), their domains and their codomains have the same normal forms. Captures
and code are not compared: `Π(n : Nat). Nat where κ1 = σ0` is `Π(n : Nat). Nat`, and a
lemma's statement is compared by what it computes to, as D30 compares functions. A
comparison that needs itself answers "not convertible" (the relation is the least one); one
that errors is an error (it used to answer "not convertible": `notes/catch-census.md`). -/
def convPi (fuel : Nat) (P Q : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .tPi cs (.pi hs ds c) := P | return false
  let .tPi cs' (.pi _ ds' c') := Q | return false
  if ds.length != ds'.length then return false
  -- D54: the erasure class, and whether it returns a borrow, are part of the Π-type (the
  -- `Unit` and data rows of [Close] may differ: `Unit` has one value, D54 refined)
  unless (← fnClass fuel' P) == (← fnClass fuel' Q) && ((← declKind fuel' P) == .ref) == ((← declKind fuel' Q) == .ref) do
    return false
  if (← get).convStack.contains (P, Q) then return false
  onCopy do
      modify fun s => { s with env := #[{}], convStack := (P, Q) :: s.convStack }
      pushFrame
      pushCaps fuel' cs
      let (pds, _) ← paramDecls fuel' cs hs ds c
      let mut ws : Array (Value × Value) := #[]
      for ((d, h), pd) in (ds.zip hs).zip pds do
        let A ← evalType fuel' d
        let w ← match A with
          | .tRef T =>
            let c ← absOf T
            let l ← freshLoan
            modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
            pure (Value.borrow l c)
          | _ => genericValue fuel' A
        let pd' ← refineDecl fuel' pd (some A) w
        pushBind h (some A) w pd'.isProof pd'
        ws := ws.push (w, A)
      let C ← evalType fuel' c
      discard popFrameRaw
      pushFrame
      pushCaps fuel' cs'
      let (pds', _) ← paramDecls fuel' cs' hs ds' c'
      for (((d', h), (w, A)), pd) in ((ds'.zip hs).zip ws.toList).zip pds' do
        let A' ← evalType fuel' d'
        unless ← conv fuel' A A' do return false
        let pd' ← refineDecl fuel' pd (some A') w
        pushBind h (some A') w pd'.isProof pd'
      let C' ← evalType fuel' c'
      conv fuel' C C'
termination_by structural fuel

/-- Structural comparison of terms (inside sealed programs, closures and Π-types),
comparing embedded values by `conv`. -/
def convT (fuel : Nat) (t u : Term) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if t == u then return true
  match t, u with
  | .val v, .val w => conv fuel' v w
  | .letIn _ a b, .letIn _ c d | .seq a b, .seq c d
  | .cong a b, .cong c d | .ascribe a b, .ascribe c d =>
    pure ((← convT fuel' a c) && (← convT fuel' b d))
  | .assign p a, .assign q b => pure (p == q && (← convT fuel' a b))
  | .matchNat p z s, .matchNat q z' s' => pure (p == q && (← convT fuel' z z') && (← convT fuel' s s'))
  | .call f as h, .call g bs h' => pure (h == h' && (← convT fuel' f g) && (← convTList fuel' as bs))
  | .succ a, .succ b | .fst a, .fst b | .snd a, .snd b | .ref a, .ref b => convT fuel' a b
  | .eq a b c, .eq d e f | .id a b c, .id d e f =>
    pure ((← convT fuel' a d) && (← convT fuel' b e) && (← convT fuel' c f))
  | .pi _ ds c, .pi _ ds' c' => pure ((← convTList fuel' ds ds') && (← convT fuel' c c'))
  | .fix _ _ ds c d b, .fix _ _ ds' c' d' b' =>
    pure (d == d' && (← convTList fuel' ds ds') && (← convT fuel' c c') && (← convT fuel' b b'))
  | .prim n as, .prim m bs => pure (n == m && (← convTList fuel' as bs))
  | .ctor t c _ ps as, .ctor u d _ qs bs => pure (t == u && c == d && (← convTList fuel' ps qs) && (← convTList fuel' as bs))
  | .tind n as, .tind m bs => pure (n == m && (← convTList fuel' as bs))
  | .matchInd p t as, .matchInd q u bs =>
    pure (p == q && t == u && (← convTList fuel' (as.map (·.2)) (bs.map (·.2))))
  | _, _ => pure false
termination_by structural fuel

/-- Two function values: compare their Π-types, their captured values, and the
observations of their generic calls, run from one shared generic environment. A
comparison that needs itself again (a recursive function stuck at its own generic
call observes only a sealed call of itself) answers "not convertible": sound, and
incomplete only for functions whose observation mentions themselves. -/
def convFn (fuel : Nat) (f g : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if (← get).convStack.contains (f, g) then return false
  let pf ← funType fuel' f none
  let pg ← funType fuel' g none
  unless ← conv fuel' pf pg do return false
  let caps : Value → List Value := fun | .clo cs _ => cs | _ => []
  unless ← convList fuel' (caps f) (caps g) do return false
  let .tPi cs (.pi hs ds c) := pf | return false
  -- a comparison that errors (e.g. a stuck block's function run at a generic argument where
  -- a pattern's sub-place does not exist, fuzz-port R3) is an error, as in `convPi`
  convFnRun fuel' f g pf cs hs ds c
termination_by structural fuel

/-- `convFn`'s observation of both functions' generic calls. -/
def convFnRun (fuel : Nat) (f g pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  onCopy do
    modify fun s => { s with env := #[{}], convStack := (f, g) :: s.convStack }
    pushFrame
    pushCaps fuel' cs
    let (pds, _) ← paramDecls fuel' cs hs ds c
    let mut args := #[]
    for ((d, h), pd) in (ds.zip hs).zip pds do
      let A ← evalType fuel' d
      let w ← match A with
        | .tRef T =>
          let c ← absOf T
          let l ← freshLoan
          modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
          pure (Value.borrow l c)
        | _ => if ← isPropV fuel' A then pure Value.proof else absOf A
      let pd' ← refineDecl fuel' pd (some A) w
      pushBind h (some A) w pd'.isProof pd'
      args := args.push w
    discard popFrameRaw
    -- D38 (v1.8): a borrow result is observed as its content, after one shared fresh
    -- value is written through it, so the owners show where it points
    let σw? ← match pf with
      | .tPi _ (.pi _ _ (.ref _)) =>
        match ← callType fuel' pf args (args.map fun _ => none) with
        | .tRef T => some <$> freshAbs T
        | _ => pure none
      | _ => pure none
    let obs (fv : Value) : M (Value × List Value) := onCopy do
      let (r, _) ← callFn fuel' false fv none args (args.map fun _ => none) false
      wholeReturned r
      match r, σw? with
      | .borrow k u, some σw =>
        pushTemp u
        pushTemp (.borrow k (.abs σw))
        endAll fuel'
        discard popTemp
        let u' ← popTemp
        pure (u', (← get).env[0]!.binds.toList.map (·.val))
      | _, _ =>
        pushTemp r
        endAll fuel'
        let r ← popTemp
        pure (r, (← get).env[0]!.binds.toList.map (·.val))
    -- D53: functions are compared as code, with their moves (fuzz-port shape (c)), wherever
    -- the comparison is asked (a statement's is erased)
    let (rf, cf) ← withRuntime (obs f)
    let (rg, cg) ← withRuntime (obs g)
    pure ((← conv fuel' rf rg) && (← convList fuel' cf cg))
termination_by structural fuel

/-- `Eq` computes (§4): reflexivity (decided by conversion) is `True`; two values built by
the same constructor give the conjunction of the equations between their fields, at the
field types instantiated at the parameters (v2.1, D52: injectivity; `S` is `Nat`'s
constructor with one field; no fields: `True`); distinct constructors of one type are
`False` (v2.0, D47). Proofs are all `⋆`, so an equation between proofs is reflexive. -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 17): `Eq` computes on values: reflexive by conversion (closed under refinement), injective and disjoint on constructor heads (which refinement keeps), stuck otherwise.
def mkEqM (fuel : Nat) (A a b : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D68: a moved place (`⊥` inside) has no content to compare: the equation is stuck, neither
  -- `⊤` nor `False`. Whether a stuck block's arm moved the place differs between an abstract and
  -- a ground run, so either answer could be wrong at some instance
  if a.hasHole || b.hasHole then
    fire .EqStuck fun _ => s!"{a} and {b}: a side holds ⊥ (D68)"
    return .tEq A a b
  if ← conv fuel' a b then return vTrue
  match a, b with
  | .succ a', .succ b' => return ← mkEqM fuel' .tNat a' b'
  | .ind t c _ ps fs, .ind u d _ qs gs =>
    if t == u && c == d && fs.length == gs.length then
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
        let blocked ← if dd.dependent c then
            (dd.indexFields c).anyM fun j => do pure !(← conv fuel' (fs.getD j .bot) (gs.getD j .bot))
          else pure false
        if blocked then fire .EqStuck fun _ => s!"{a} and {b}: index fields not convertible (D64)"
        if !blocked then
          if dd.dependent c then fire .EqInj fun _ => s!"{a} and {b}: index fields convertible (D64)"
          let Ts ← fieldTypesOf fuel' dd args c fs
          if Ts.length == fs.length then
            let eqs ← ((Ts.map (·.2)).zip (fs.zip gs)).mapM fun (T, (v, w)) => mkEqM fuel' T v w
            return andList eqs
  | _, _ => pure ()
  if distinctCtors a b then pure vFalse
  else pure (.tEq A a b)
termination_by structural fuel

-- ### Evaluation

/-- D60 [Rewrite]: the goal `G` of `rewrite h in t` after the rewrite, i.e. the type `t`
must have. With `h : Eq A a b`, every occurrence of `b`'s normal form in `G` is generalised
to a fresh `σ` (the replacement [Split] uses to generalise a sealed program, D34, here local
to the goal and not recorded), and `a` is substituted for `σ`, re-normalising what changed.
`rev` (`rewrite ← h in t`) swaps `a` and `b`. The term is `J(A, a, b, λz. G[z/b], h, t)`
with the motive read off the goal. A rewrite that finds nothing to rewrite leaves the goal
as it is (rule-audit C22), so a wrong direction shows as a goal `t` does not prove; an `h`
whose type computes to `True` rewrites nothing either (its two sides are already equal). -/
def rewriteGoal (fuel : Nat) (rev : Bool) (h : Term) (G : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  unless (← typeClass fuel' G) == 2 do err s!"rewrite: the goal {G} is not a proposition"
  let (_, Th) ← eval fuel' true h
  match Th.map unitTop with
  | some (.tInd "True" []) => pure G
  | some (.tEq A a b) =>
    let (src, dst) := if rev then (a, b) else (b, a)
    let σ ← freshAbs A
    let G1 ← substV fuel' src (.abs σ) G
    -- [T-Rewrite] has no premise that `b` occurs: a rewrite that finds nothing leaves the goal
    -- as it is (G' = G), and `t` is checked against it (rule-audit C22)
    let G' ← substV fuel' (.abs σ) dst G1
    trace fun _ => s!"[Rewrite] {src} ↦ {dst}: goal {G'}"
    pure G'
  | some T => err s!"rewrite: the proof has type {T}, which is not an equation"
  | none => err "rewrite: untyped proof"
termination_by structural fuel

def expectTy (fuel : Nat) (what : String) (T : Option Value) (A : Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if let some T := T then
    unless ← conv fuel' T A do err s!"{what} has type {T}, expected {A}"
termination_by structural fuel

/-- P2 (v1.3, D26): erased terms leave no trace. A term whose type is a proposition is
evaluated on a private copy of Ω, argument evaluation included, and the copy is
discarded. Every value of a proposition is `⋆` (C7) and only such terms evaluate to
`⋆`, so this is decided on the value, in both modes. -/
def eval (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- the editor: an error here is reported at `t`, and hovering `t` shows its value
  located t (noteValue t (evalAt fuel' typed t hint))
termination_by structural fuel

def evalAt (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let before := (← get).env
  -- the erasure pre-pass: decided before the term runs, from declared types (a call's
  -- head is not classified: its flags are the call's)
  let head := (← get).headEval
  let hinted := (← get).tailDecl     -- a sequencing form hands its reading to its tail
  modify fun s => { s with headEval := false, tailDecl := none }
  let d? ← if !head && !(t matches .val _) then
      match hinted with
      | some d => pure (some d)
      | none => some <$> withLive true (declOf fuel' false [] [] t)
    else pure none
  modify fun s => { s with curDecl := d? }
  let pre ← match d? with
    | some d => preFlags t d
    | none => pure none
  -- D53: an erased term's reads copy, decided before it runs
  -- (tracked with or without D53: K2/K3 read it too)
  let typing0 := (← get).typing
  modify fun s => { s with typing := typed }
  -- D68: an erased term is a statement: it runs on its own private
  -- copy of the state, so what it moves, writes or borrows is undone with the copy, as at
  -- runtime, where it does not run at all
  let erasedHere := pre matches some (true, _)
  let run : M (Value × Option Value) := withErasedIf erasedHere (evalCore fuel' typed t hint)
  let r ← onFail (if erasedHere then do
        -- the classification flags the term set are its own, not the copy's
        let (r, fl) ← onCopy (do let r ← run; pure (r, ← getFlags))
        setFlags fl
        pure r
      else run)
    (modify fun s => { s with typing := typing0 })
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
  let (erased, proof) ← match t with
    | .call _ _ _ => getFlags      -- set by `callFn` from the callee's class
    | .seq _ _ | .letIn _ _ _ | .matchNat _ _ _ | .matchInd _ _ _ =>
      let (_, p) ← getFlags
      pure (p, p)
    | .cong _ _ | .prim "trans" _ | .prim "symm" _ => pure (true, true)
    | .prim "hole" _ => getFlags     -- set by `evalCore`: a proof iff its type is a proposition
    | .prim "rewrite" _ | .prim "rewriteR" _ => pure (true, true)   -- D60: `J`, a proof
    | .ctor ty _ _ _ _ => let p ← ctorIsProof ty; pure (p, p)   -- D42: a Prop inductive's value is a proof
    | .prim "J" [_, _, _, P, _, _] =>
      let p ← jErased fuel' P      -- the appendix's clause 4: the motive is syntactically into Prop
      pure (p, p)
    | .ascribe (.val .proof) _ => pure (true, true)
    | .ascribe _ A =>
      -- a proof if the ascribed term is, or if the annotation's declared sort is Prop
      let p := (← getFlags).2 || (← withLive true (typeDecl fuel' false [] [] A)).isProof
      pure (p, p)
    | .place _ | .const _ | .val _ | .fix .. =>
      let p ← leafProof fuel' t r.1
      pure (p, p)
    | _ => pure (false, false)
  -- the after-the-fact classification is kept as an assertion that the two agree
  let (erased, proof) ← match pre with
    | some f =>
      if f != (erased, proof) then
        err s!"INTERNAL [pre-pass] {t.pp []}: erased/proof = {f} by its declared type, {(erased, proof)} after running (please report)"
      pure f
    | none => pure (erased, proof)
  if erased then
    modify fun s => { s with env := before }
  setFlags (erased, proof)
  pure r
termination_by structural fuel

/-- `hint`: the type the context requires of `t`, used only to infer the parameters of a
constructor application that its fields do not determine (v2.0, D46). -/
def evalCore (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  tick
  let ty (T : Value) : Option Value := if typed then some T else none
  match t with
  | .place p =>
    let T ← if typed then some <$> placeType fuel' p else pure none
    if let some T := T then repackAt fuel' p T "read whole"
    pure (← readPlace fuel' p, T)
  | .borrow p =>
    let T ← if typed then some <$> placeType fuel' p else pure none
    if let some T := T then
      if T.typeHasRef then err s!"&{← ppPlace p}: a borrow of a borrow-typed place"
      -- D66 for terms ([T-Borrow]'s premise, reviewer-6's A12): the borrowed place's type
      -- is in Type₀, as for the type former `&A`
      if !(← isBorrowable fuel' T) then
        err s!"[D66] &{← ppPlace p}: its type {T} is not in Type₀ (only runtime types are borrowed: never a proposition, Prop, a universe, or a type not known to be in Type₀)"
      repackAt fuel' p T "borrowed whole"
    let b ← borrowPlace fuel' p
    openWrite p
    pure (b, T.map .tRef)
  | .assign p u =>
    if typed then
      if let some r ← lentProofAssign fuel' p u then return r
    -- the place's type is the type the context requires of a constructor's parameters and of an
    -- embedded value with no type of its own (an inert loan in a sealed program's `*r := loan`)
    let hint ← if typed && (u matches .ctor .. | .val _) then
        placeType? fuel' p
      else pure none
    -- the place's type, read before the value is evaluated: evaluating it may move the place's
    -- content out (`*x := match *x {…}`, D68), and an untyped frame types a place by its content
    let Tp0 ← if typed then placeType? fuel' p else pure none
    let (v, Tv) ← eval fuel' typed u hint
    -- D64 [Open]: a field whose declared type mentions earlier fields takes any value (a strong
    -- update: while its value is open it is typed by what it holds); [Repack] checks it later
    -- [Open]: a strong update
    if typed && (← strongUpdate p) then fire .Open fun _ => s!"a strong update of a dependent field, to a value of type {Tv.getD .bot}"
    if typed && !(← strongUpdate p) then
      expectTy fuel' "the assigned value" Tv (← match Tp0 with | some T => pure T | none => placeType fuel' p)
    assignPlace fuel' p v
    openWrite p
    pure (.unit, ty .tUnit)
  | .letIn h u w =>
    let myD := (← get).curDecl
    let du ← withLive true (declOf fuel' false [] [] u)
    let (v, T) ← eval fuel' typed u
    let du' ← refineDecl fuel' du T v
    -- `h` is a proof iff `u` is, or its declared type is a proposition (P1; `u` may be an
    -- embedded value, `⋆` in a sealed program's bindings, which the pre-pass does not read)
    let p := (← getFlags).2 || du'.isProof
    pushBind h T v p du'
    -- the tail's reading is this let's (read with `h`'s declared type, unless refined)
    if du' == du then modify fun s => { s with tailDecl := myD }
    let (r, R) ← eval fuel' typed w
    let fl ← getFlags     -- the body's erasure flags (dropping may normalise)
    pushTemp r
    dropTopBind fuel'
    setFlags fl
    pure (← popTemp, R)
  | .seq u w =>
    let myD := (← get).curDecl
    let (v, _) ← eval fuel' typed u
    dropValue fuel' v
    modify fun s => { s with tailDecl := myD }     -- the tail's reading is this sequence's
    eval fuel' typed w
  | .matchNat p z s => evalMatch fuel' typed p z s
  | .matchInd p ty arms => evalMatchInd fuel' typed p ty arms
  | .tind n as => evalTInd fuel' typed n as
  | .ctor ty c h ps as => evalCtor fuel' typed ty c h ps as hint
  | .const n =>
    let g ← lookupGlobal n
    let v ← if ← isPropV fuel' g.ty then pure .proof else pure g.val
    pure (v, some g.ty)
  | .val v =>
    if !typed then return (v, none)
    -- an embedded value with no type of its own (a proof, an inert loan) has the type of the
    -- position it was embedded at: a parameter's or a field's declared type (the hint)
    match v, hint with
    | .proof, some T => if ← isPropV fuel' T then pure (v, some T) else pure (v, some (← valType fuel' v))
    | .loan _, some T => pure (v, some ((← valType? fuel' v).getD T))
    | _, _ => pure (v, some (← valType fuel' v))
  | .sort l => pure (.sort l, some (.sort (sortSucc l)))
  | .pi _ ds c =>
    borrowParamCheck ds c
    -- a type former is erased: even its captures (which access places) run on a copy
    let (cs, t') ← onCopy (withErased (capture fuel' t))
    let T := Value.tPi cs t'
    if !typed then return (T, none)
    -- [T-Pi] runs the parameter types and the codomain (typing); the decisions read the same
    -- sort off the terms (`Decide.sortOf`, D55: a type's declared sort is its computed sort).
    -- The two are asserted to agree, as the erasure pre-pass is against the after-the-fact
    -- classification (`notes/two-paths-census.md`)
    let l ← piSort fuel' T
    let l' ← sortOf fuel' T
    unless l == l' do
      err s!"INTERNAL [D55] the Π-type {T} has sort {l} by running its parameter types and codomain, {l'} by their declared types (please report)"
    pure (T, some (.sort l))
  | .fix _ hs ds c _ _ =>
    borrowParamCheck ds c
    -- a closure whose calls are erased is itself erased by the pre-pass (its captures copy)
    let (cs, t') ← capture fuel' t
    let v := Value.clo cs t'
    let T := match t' with
      | .fix _ _ ds' c' _ _ => Value.tPi cs (.pi hs ds' c')
      | _ => Value.tPi cs (.pi hs ds c)
    if typed then checkFix fuel' v cs t'
    let v ← if ← isPropV fuel' T then pure .proof else pure v
    pure (v, some T)
  | .call f as hd => evalCall fuel' typed f as hd
  | .nat => pure (.tNat, some (.sort 1))
  | .unit => pure (.tUnit, some (.sort 1))
  | .zero => pure (.zero, ty .tNat)
  | .tt => pure (.unit, ty .tUnit)
  | .succ u =>
    let (v, T) ← eval fuel' typed u
    expectTy fuel' "the argument of S" T .tNat
    pure (.succ v, ty .tNat)
  | .fst u | .snd u =>
    -- `t.1`, `t.2` of a term that is not a place: field 1 or 2 of a pair (D52)
    let (v, T) ← eval fuel' typed u
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
    -- each side is a statement position: it runs on its own private copy of the state, so
    -- its effects are visible to the rest of that side and to nothing else (one copy per side)
    let A' ← evalType fuel' A
    let (va, Ta) ← onCopy (eval fuel' typed a)
    let (vb, Tb) ← onCopy (eval fuel' typed b)
    expectTy fuel' "the left side of Eq" Ta A'
    expectTy fuel' "the right side of Eq" Tb A'
    pure (← mkEqM fuel' A' va vb, some (.sort 0))
  | .cong f h =>
    let (fv, fT) ← eval fuel' typed f
    let (_, Th) ← eval fuel' typed h
    if !typed then return (.proof, none)
    match Th.map unitTop with
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    | some (.tEq A a b) =>
      let (fa, B) ← callFn fuel' true fv fT #[a] #[some A] false
      let (fb, _) ← callFn fuel' true fv fT #[b] #[some A] false
      pure (.proof, some (← mkEqM fuel' B.get! fa fb))
    | some T => err s!"cong: the proof has type {T}, which is not an equation"
    | none => err "cong: untyped proof"
  | .ref A =>
    let A' ← evalType fuel' A
    if A'.typeHasRef then err "&A needs A borrow-free (RULES §1)"
    -- D66: only `A : Type₀` is borrowed, so `&A : Type₀` cannot make Type₀ impredicative
    if !(← isBorrowable fuel' A') then
      err s!"[D66] &{A'}: {A'} is not in Type₀ (only runtime types are borrowed: never a proposition, Prop, a universe, or a type not known to be in Type₀)"
    pure (.tRef A', some (.sort 1))
  | .id A a b => pure (← withErased (idType fuel' typed A a b), some (.sort 0))
  | .prim "J" [A, a, b, P, h, u] =>
    -- J(A, a, b, P, h, t) : P(b) for h : Eq A a b and t : P(a) (endpoints explicit, D23)
    if !typed then
      if !(← jErased fuel' P) then
        -- its endpoints are erased positions, on private copies; `A`, `P` and `h`
        -- are never run by the machine (A.191)
        let (av, _) ← stmtCopy (eval fuel' false a)
        let (bv, _) ← stmtCopy (eval fuel' false b)
        -- [J]: the endpoints are convertible, `J` is `t`; [J-stuck]: otherwise the run is
        -- stuck, and `t` does not run (D56, D63, rule-audit item 5)
        if ← conv fuel' av bv then return ← eval fuel' false u
        stuckNow
      return (← eval fuel' false u)
    let A' ← evalType fuel' A
    let (av, Ta) ← stmtCopy (eval fuel' true a)
    let (bv, Tb) ← stmtCopy (eval fuel' true b)
    expectTy fuel' "J's first endpoint" Ta A'
    expectTy fuel' "J's second endpoint" Tb A'
    let (Pv, PT) ← stmtCopy (eval fuel' true P)
    let (_, Th) ← eval fuel' true h
    let hT ← mkEqM fuel' A' av bv
    expectTy fuel' "J's equation" Th hT
    let (Pa, _) ← callFn fuel' true Pv PT #[av] #[some A'] false
    let (Pb, _) ← callFn fuel' true Pv PT #[bv] #[some A'] false
    if !(← jErased fuel' P) && !(← conv fuel' av bv) then
      -- [T-J-stuck]: the machine would be stuck, so typing checks `t` against `P(a)` on a
      -- private copy and closes the `J` off as a stuck block of type `P(b)`, as [Split] closes
      -- off a stuck match; its sealed programs run `t` once a refinement makes the endpoints
      -- convertible (D63, rule-audit item 5)
      -- the endpoints, motive and equation are erased positions, formed once here: the block
      -- embeds their values and captures only `t`'s places. Its one arm is `t`, so the block
      -- returns where `t` ends, and `closeBlock` checks it there as it checks a match's arms
      -- (D75, D76: a `t` that wrote an index field of a place the block takes by `&` left the
      -- place open on the direct path while the generic path split the block's sealed
      -- program as whole, `JBlocks.BoomJ`)
      let tJ := Term.prim "J" [.val A', .val av, .val bv, .val Pv, .ascribe (.val .proof) (.val hT), u]
      let arm : BlockArm := ⟨pure .unit, fun _ => do
        let (tv, Tu) ← eval fuel' true u (some Pa)
        let fl ← getFlags
        expectTy fuel' "the transported term" Tu Pa
        setFlags fl
        pure (tv, Pa)⟩
      return ← closeBlock fuel' tJ [arm] (some Pb)
    let (v, Tu) ← eval fuel' true u
    let fl ← getFlags
    expectTy fuel' "the transported term" Tu Pa
    setFlags fl    -- t's flags (J is t)
    pure (v, some Pb)
  | .prim "symm" [h] =>
    let (_, Th) ← eval fuel' typed h
    match Th.map unitTop with
    | some (.tEq A a b) => pure (.proof, some (← mkEqM fuel' A b a))
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    -- an equation that computes to `False` (a refinement made it impossible) is symmetric
    -- to one that does too (fuzz-port R7)
    | some (.tInd "False" []) => pure (.proof, some (.tInd "False" []))
    | _ => if typed then err "symm: not an equation" else pure (.proof, none)
  | .prim "trans" [h, k] =>
    let (_, Th) ← eval fuel' typed h
    let (_, Tk) ← eval fuel' typed k
    if !typed then return (.proof, none)
    match Th.map unitTop, Tk.map unitTop with
    | some (.tInd "True" []), some T | some T, some (.tInd "True" []) => pure (.proof, some T)
    | some (.tInd "False" []), _ | _, some (.tInd "False" []) => pure (.proof, some (.tInd "False" []))
    | some (.tEq A a b), some (.tEq A' b' c) =>
      unless (← conv fuel' A A') && (← conv fuel' b b') do err s!"trans: {Th.get!} and {Tk.get!} do not compose"
      pure (.proof, some (← mkEqM fuel' A a c))
    | _, _ => err "trans: not equations"
  | .prim "rewrite" [h, u] | .prim "rewriteR" [h, u] =>
    -- D60 [Rewrite]: checked against the type the context requires (`hint`)
    if !typed then return (.proof, none)
    let some G := hint
      | err "rewrite: the goal is not known here (use it in tail position, as a call's argument, or under an annotation `let x : T = …`)"
    let G' ← rewriteGoal fuel' (t matches .prim "rewriteR" _) h G
    let (_, Tu) ← eval fuel' true u (some G')
    expectTy fuel' "the rewritten term" Tu G'
    pure (.proof, some G)
  | .prim "split" _ | .prim "splitArms" _ => err "split: only in tail position (where the goal is known)"
  | .prim "hole" _ =>
    -- a hole (`?`, docs/07): a value of the type the context requires (a fresh abstract value,
    -- `⋆` for a proposition), so the rest checks around it; the editor shows its goal and Ω.
    -- A run that reaches it is stuck
    if !typed then stuckNow
    let some G := hint
      | err "?: the type expected here is not known (write the hole in tail position, as a call's argument, or under an annotation)"
    noteHole t G
    let p ← isPropV fuel' G
    setFlags (p, p)
    pure (← if p then pure Value.proof else absOf G, some G)
  -- D53: `clone(p)` copies `p` (an erased read); `peek` is an observation's final read
  | .prim "clone" [u] =>
    -- K2: cloning a view at runtime copies it
    if let .place p := u then
      if let some v ← content? p then unsizedCheck p v "cloned"
    withCopying (withErased (eval fuel' typed u hint))
  | .prim "peek" [u] => withCopying (withErased (eval fuel' typed u hint))
  | .prim "inplace" [t] =>
    if t matches .place _ then modify fun s => { s with inPlace := true }
    let r ← eval fuel' typed t hint
    modify fun s => { s with inPlace := false }
    pure r
  | .prim n _ => err s!"unknown primitive {n}"
  | .ascribe (.val .proof) A =>     -- a captured proof, inlined with its type (`capture`)
    if typed then pure (.proof, some (← evalType fuel' A)) else pure (.proof, none)
  | .ascribe u A =>
    if !typed then return (← eval fuel' false u)
    let A' ← evalType fuel' A
    let (v, T) ← match u with
      | .matchNat p z s => evalMatch fuel' true p z s (some A')
      | .matchInd p ty arms => evalMatchInd fuel' true p ty arms (some A')
      | _ => eval fuel' true u (some A')      -- the annotation is a hint for a constructor's parameters
    let fl ← getFlags
    expectTy fuel' "the ascribed term" T A'
    setFlags fl
    pure (v, some A')
termination_by structural fuel

/-- D64 amended ([Open]): `p := u` for a proof field of a dependent constructor value while part
of the value is lent (a live loan in its fields). The proof is about the whole value, and a live
borrow can still write its part, which nothing would then invalidate: the write goes through the
borrow, not through a field place, and [Repack] cannot check a proof, `⋆`. So the assignment is
checked on a private copy in which each such borrow holds a fresh abstract value of its type:
the proof must hold whatever the borrow leaves there. `none`: not this case (the ordinary
[Assign] path checks it). -/
def lentProofAssign (fuel : Nat) (p : Place) (u : Term) : M (Option (Value × Option Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .field g q := p | return none
  let some d := (← get).inds.find? (·.name == g.ty) | return none
  unless d.dependent g.ctor && (← fieldIsProof g) do return none
  let cv := (← content? q).getD .bot
  let some fs ← ctorFields cv g | return none
  let env := (← get).env
  let ls := (fs.flatMap fun w => liveLoansIn env w).eraseDups
  if ls.isEmpty then return none
  fire .Open fun _ => s!"the proof field {g.name} is assigned while borrows {ls} lend part of its value: checked with what they hold unknown"
  onCopy do
    for l in ls do
      let env := (← get).env
      let some pos := findBorrow env l | continue
      let some (c, _) := (valAt env pos).takeBorrow l | continue
      let some T ← valType? fuel' c
        | err s!"[Open] the proof field {g.name} is assigned while its value is lent, and the type of what the borrow holds ({c}) is not known"
      let σ ← absOf T
      setAt pos ((valAt env pos).setBorrowContent l σ)
    let T ← placeType fuel' p
    let (_, Tv) ← eval fuel' true u (some T)
    expectTy fuel' s!"the proof assigned to {g.name} (while part of its value is lent, what the borrow holds unknown: [Open])" Tv T
  assignPlace fuel' p .proof
  openWrite p
  pure (some (.unit, some .tUnit))
termination_by structural fuel

/-- `D(ā)` (v2.0, D46): the arguments stand in type positions, so each is evaluated on a
private copy (P2); when typed, each is checked against its parameter's type,
evaluated with the earlier parameters bound. Its sort is the declared one. -/
def evalTInd (fuel : Nat) (typed : Bool) (n : String) (as : List Term) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let d ← lookupInd n
  if as.length != d.params.length then
    err s!"{n} takes {d.params.length} parameters, given {as.length}"
  let (vs, tys) ← evalParams fuel' n as typed
  if typed then checkParams fuel' d n vs tys
  pure (.tInd n vs.toList, if typed then some (.sort d.sort) else none)
termination_by structural fuel

/-- Parameters are type positions: each on a private copy (P2). -/
def evalParams (fuel : Nat) (n : String) (as : List Term) (typed : Bool) :
    M (Array Value × Array (Option Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let mut vs := #[]
  let mut tys := #[]
  for a in as do
    let (v, T) ← stmtCopy (eval fuel' typed a)
    vs := vs.push v
    tys := tys.push T
  pure (vs, tys)
termination_by structural fuel

/-- Each parameter against its declared type, evaluated with the earlier ones bound; no
borrow types (no borrows inside data). -/
def checkParams (fuel : Nat) (d : IndDecl) (n : String) (vs : Array Value) (tys : Array (Option Value)) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  onCopy do
    pushFrame
    for (((h, PT), v), T) in (d.params.zip vs.toList).zip tys.toList do
      let A ← evalType fuel' PT
      expectTy fuel' s!"the parameter {h.name} of {n}" T A
      noBorrowParam n v
      let pd' ← withLive true (typeDecl fuel' false [] [] PT)
      pushBind h (some A) v pd'.isProof pd'
termination_by structural fuel

/-- A constructor application `C(ā; t₁, …, tₖ)` of `D` (v2.0, D49 (4): the parameters `ā`
lead, surface `C[ā](t̄)`, and may be omitted). Its value is `C(ā; v̄)`, recording the
parameters when known, or `⋆` when `D` is a Prop inductive (D42). When typed, omitted
parameters are inferred from the fields' types, and those no field determines from
`hint` (the type the context requires: an annotation, the goal, a parameter or field
type). An untyped run records the parameters only when they are written. -/
def evalCtor (fuel : Nat) (typed : Bool) (ty : String) (c : Nat) (h : Hint) (pts : List Term) (as : List Term)
    (hint : Option Value) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let d ← lookupInd ty
  if d.abstract && (← atRuntime) then
    err s!"[K3] the constructor {h.name} of the abstract type {ty} at runtime, outside model code (an `implemented by` body, or a function taking or returning an unsized value)"
  let some (_, fields) := d.ctors[c]? | err s!"{ty} has no constructor {c}"
  if fields.length != as.length then err s!"{h.name} takes {fields.length} fields, given {as.length}"
  let np := d.params.length
  if !pts.isEmpty && pts.length != np then err s!"{h.name} takes {np} parameters, given {pts.length}"
  let (evs, etys) ← evalParams fuel' ty pts typed
  if typed && !pts.isEmpty then checkParams fuel' d ty evs etys
  let mut sol : Array (Option Value) := if !pts.isEmpty then evs.map some else match hint with
    | some (.tInd m ps) => if m == ty && ps.length == np then (ps.map some).toArray else Array.replicate np none
    | _ => Array.replicate np none
  let mut tys := #[]
  let mut ws0 : Array Value := #[]
  -- D64: a dependent field's hint is its type at the fields evaluated so far
  let dep := d.dependent c
  -- one mental model: a proof constructor's arguments are statement positions
  let stmtC ← ctorIsProof ty
  for ((a, (_, FT)), i) in (as.zip fields).zipIdx do
    let fh ← if typed && ((np > 0 && (a matches .ctor .. | .prim "rewrite" _ | .prim "rewriteR" _)) || (a matches .val _)
        || (dep && d.fieldDependent c i))
      then fieldTypeAt fuel' d sol c i ws0.toList else pure none
    let (w, T) ← stmtArgIf stmtC (eval fuel' typed a fh)
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
  for (T, (fname, FT)) in tys.toList.zip (← fieldTypesOf fuel' d ps.toList c ws.toList) do
    expectTy fuel' s!"field {fname} of {h.name}" T FT
  let v := if proof then Value.proof else .ind ty c h ps.toList ws.toList
  pure (v, some (.tInd ty ps.toList))
termination_by structural fuel

-- ### Calls: [Call], P5, [Call-type], [Close], [Rec]

/-- One mental model: does `fv` return a type or a proof (its class, D28/D35)? Its arguments are
then statement positions. -/
def stmtCallee (fuel : Nat) (fv : Value) (fT : Option Value) (cls? : Option Nat) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if let some k := cls? then return k != 0
  match ← funType? fuel' fv fT with
  | some T => pure ((← fnClass fuel' T) != 0)
  -- a proof is only ever called at a proposition (P5): its calls return proofs. Any other value
  -- with no readable Π-type is not callable, and `callFn` rejects the call
  | none => pure (fv == .proof)
termination_by structural fuel

def evalCall (fuel : Nat) (typed : Bool) (f : Term) (as : List Term) (head : Bool)
    (cls? : Option Nat := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  modify fun s => { s with headEval := true }
  -- D53 (e): a call does not consume the function it calls (read in place)
  if f matches .place _ then modify fun s => { s with inPlace := true }
  let (fv, fT) ← eval fuel' typed f
  modify fun s => { s with inPlace := false }
  pushTemp fv
  -- one mental model: a call that returns a type or a proof is a statement, and each of its
  -- arguments a statement position, run on its own private copy of the state
  let stmt ← stmtCallee fuel' fv fT cls?
  let mut tys := #[]
  let mut ws0 := #[]
  let mut ender := #[]     -- the editor: which argument ended each argument's borrow
  for a in as do
    -- v2.0: a constructor argument's parameters may come from the parameter's type
    let hint ← if typed && (a matches .ctor .. | .val _ | .prim "rewrite" _ | .prim "rewriteR" _ | .prim "hole" _) then argHint fuel' fv fT ws0 else pure none
    let (w, T) ← stmtArgIf stmt (eval fuel' typed a hint)
    pushTemp w
    ws0 := ws0.push w
    ender ← noteEnders ender ws0
    tys := tys.push T
  let ws ← popTemps as.length
  let fv ← popTemp
  atLoc (← enderLoc ender ws) <| callFn fuel' typed fv fT ws tys head cls?
termination_by structural fuel

/-- The type of the next parameter of `fv`, with the earlier ones bound to the arguments
evaluated so far (a hint for a constructor argument's parameters; `none` if unknown). -/
def argHint (fuel : Nat) (fv : Value) (fT : Option Value) (ws : Array Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some (.tPi cs (.pi hs ds c)) ← funType? fuel' fv fT | return none
  let some d := ds[ws.size]? | return none
  onCopy do
    pushFrame
    pushCaps fuel' cs
    let (pds, _) ← paramDecls fuel' cs hs ds c
    for (((d', h), w), pd) in ((ds.zip hs).zip ws.toList).zip pds do
      let A ← evalType fuel' d'
      let pd' ← refineDecl fuel' pd (some A) w
      pushBind h (some A) w pd'.isProof pd'
    some <$> evalType fuel' d
termination_by structural fuel

/-- The Π-type of a function value, or `none` when it has none that can be read: a sealed
function whose program's typing gives no type, or a value that is not a function (`⋆` is
called only as a proof, P5). A total query. -/
def funType? (fuel : Nat) (fv : Value) (fT : Option Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if let some T := fT then return some T
  match fv with
  | .gfn n => pure (some (← lookupGlobal n).ty)
  | .clo cs (.fix _ hs ds c _ _) => pure (some (.tPi cs (.pi hs ds c)))
  | .abs σ => some <$> absType σ
  -- D56: a stuck cast can be a function; its type is its program's (`sealedType?`)
  | .sealed _ => valType? fuel' fv
  | _ => pure none
termination_by structural fuel

/-- The Π-type of a function value, which must be readable (`funType?`). -/
def funType (fuel : Nat) (fv : Value) (fT : Option Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← funType? fuel' fv fT with
  | some T => pure T
  | none => match fv with
    | .sealed _ =>
      err s!"the type of the sealed function {fv} is not known here (a call of a sealed function in untyped code)"
    | _ => err s!"{fv} is not a function"
termination_by structural fuel

/-- The row of [Close]'s table (and whether P5 applies), syntactically when possible. -/
def resultKind (fuel : Nat) (piTy : Value) (ws : Array Value) : M Kind := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match piTy with
  | .tPi _ (.pi _ _ c) =>
    match c with
    | .val B => kindOf fuel' B
    | _ => match syntacticKind? c with
      | some k => pure k
      | none => kindOf fuel' (← callType fuel' piTy ws (ws.map fun _ => none))
  | _ => err s!"not a function type: {piTy}"
termination_by structural fuel

/-- [Call-type]: the result type is `B` evaluated at the call point (after the
arguments are evaluated) with each parameter bound to its argument's value (a borrow
argument moved into it). The other free variables of `B` were captured when the
Π-type was formed. Each argument is checked against its parameter's type. -/
def callType (fuel : Nat) (piTy : Value) (ws : Array Value) (tys : Array (Option Value)) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .tPi cs (.pi hs ds c) := piTy | err s!"not a function type: {piTy}"
  if ds.length != ws.size then err s!"arity: {ds.length} parameters, {ws.size} arguments"
  let pf ← paramFlags fuel' cs ds
  let argLocs := (← get).locs.callArgs     -- the editor: the arguments' ranges
  onCopy <| unlocated do     -- the callee's parameter types are not this point's code
    pushFrame
    pushCaps fuel' cs
    let (pds, _) ← paramDecls fuel' cs hs ds c
    for (((d, h), i), pd) in ((ds.zip hs).zipIdx).zip pds do
      let A ← evalType fuel' d
      noteLoc argLocs[i]?.join (.expected A)
      atLoc argLocs[i]?.join <| expectTy fuel' s!"argument {i + 1} ({h.name})" tys[i]! A
      pushBind h (some A) ws[i]! (pf.getD i false) (← refineDecl fuel' pd (some A) ws[i]!)
    evalType fuel' c
termination_by structural fuel

/-- P5: the borrow arguments of a call that is not run end unchanged. -/
def endBorrowArgs (fuel : Nat) (ws : Array Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for w in ws do
    if let .borrow l _ := w then
      pushTemp w
      endBorrow fuel' l
      discard popTemp
termination_by structural fuel

/-- [Call]: push a frame `[caps, self, x̄ ↦ w̄]`, run the body, pop the frame. -/
def runBody (fuel : Nat) (fv : Value) (cs : List Value) (t : Term) (ws : Array Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .fix self hs ds c _ body := t | err "internal: not a fix"
  -- K2/K3: a model function's body never runs at runtime
  let model ← match fv with
    | .gfn n => do pure (← lookupGlobal n).model
    | _ => pure false
  if model then modify fun s => { s with modelDepth := s.modelDepth + 1 }
  let r ← onFail (runBodyCore fuel' fv cs t ws self hs ds c body)
    (if model then modify fun s => { s with modelDepth := s.modelDepth - 1 } else pure ())
  if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }
  pure r
termination_by structural fuel

def runBodyCore (fuel : Nat) (fv : Value) (cs : List Value) (t : Term) (ws : Array Value) (self : Hint)
    (hs : List Hint) (ds : List Term) (c : Term) (body : Term) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let d := (← get).depth
  if d ≥ 2000 then exhausted "call depth exceeded (a non-terminating recursion)"
  modify fun s => { s with depth := d + 1 }
  let pf ← paramFlags fuel' cs ds
  let (pds, cd) ← paramDecls fuel' cs hs ds c
  -- a proof parameter that a function or Π-type in the body may capture needs its type,
  -- which is all a captured proof records (`capture`): read it off the declared domain,
  -- at the arguments (arrays-library: a Π whose body uses a proof captured from outside it)
  let ptys ← if body.formsFn && (pf.any id || pds.any (·.isProof)) then onCopy do
      pushFrame
      pushCaps fuel' cs
      let mut out := #[]
      for ((((h, w), p), pd), d) in (((hs.zip ws.toList).zip pf).zip pds).zip ds do
        let A? ← if p || pd.isProof then some <$> evalType fuel' d else pure none
        out := out.push A?
        pushBind h A? w p pd
      pure out
    else pure #[]
  pushFrame
  pushCaps fuel' cs
  pushBind self none fv false (.pi cd)
  for ((((h, w), p), pd), i) in (((hs.zip ws.toList).zip pf).zip pds).zipIdx do
    pushBind h (ptys[i]?.getD none) w p (← refineDecl fuel' pd none w)
  -- D53: a body is code; a function whose calls are erased has an erased body (b)
  let erasedFn := (← fnClass fuel' (← funType fuel' fv none)) != 0
  let (v, _) ← withErasedIf erasedFn (eval fuel' false body)
  wholeReturned v
  pushTempAt ((← topIdx) - 1) v
  popFrame fuel'
  modify fun s => { s with depth := d }
  popTemp
termination_by structural fuel

def callFn (fuel : Nat) (typed : Bool) (fv : Value) (fT : Option Value) (ws : Array Value)
    (tys : Array (Option Value)) (head : Bool) (cls? : Option Nat := none) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if let some i := ws.findIdx? (· == .bot) then
    err s!"[Call] argument {i + 1} is ⊥ at the call point (a later argument ended its borrow): an argument not of the parameter's type"
  -- A proof value is only ever called at a proposition: P5, not run.
  if fv == .proof then
    let B ← if typed then some <$> callType fuel' (← funType fuel' fv fT) ws tys else pure none
    endBorrowArgs fuel' ws
    setFlags (true, true)
    return (.proof, B)
  let piTy ← funType fuel' fv fT
  let B ← if typed then some <$> callType fuel' piTy ws tys else pure none
  if typed then
    trace fun _ => s!"[Call-type] {fv}({", ".intercalate (ws.toList.map toString)}) : {B.getD .bot}"
    recCheck fv ws
  -- D54: the class and [Close] row are those of the function value's own declared Π-type,
  -- on every path (conversion only lets a value stand at a Π-type of its class and row, so
  -- this is also the static type's; a sealed function whose own type cannot be read here
  -- keeps the static one)
  let clsTy := (← funType? fuel' fv none).getD piTy
  -- [Close]'s row: v1.7 (D35) from the declared codomain
  let kind ← declKind fuel' clsTy
  -- D28, D35: the callee's class, read off its declared codomain (a stuck block's is
  -- given by `closeBlock`)
  let cls ← match cls? with
    | some k => pure k
    | none => fnClass fuel' clsTy
  let kind := if kind == .prop then Kind.data else kind
  -- D53: an erased call cannot make whole a borrow it is passed (its effects vanish at runtime)
  if cls != 0 then wholeBorrowArgs ws "an erased call"
  if cls == 2 then
    endBorrowArgs fuel' ws
    setFlags (true, true)
    return (.proof, B)
  let r ← match fv with
    | .abs _ | .sealed _ =>
      -- a neutral head closes off at once (v1.3), except as [Seal]'s head call (D39)
      if head then stuckNow else closeCall fuel' fv ws kind B
    | .gfn _ | .clo _ _ =>
      let (cs, t) ← fixOf fv
      -- [App-close]: a stuck body closes the call off; [App-head]: not a sealed program's head call
      catchStuck (runBody fuel' fv cs t ws) fun on =>
        if head then throw (.stuck on) else closeCall fuel' fv ws kind B
    | _ => err s!"call of {fv}, which is not a function"
  let r := if cls == 2 then Value.proof else r
  setFlags (cls != 0, cls == 2)
  pure (r, B)
termination_by structural fuel

/-- D59 refined: a stuck call's result has type `Unit`: its declared codomain says so, or its
type as computed at the call (`B` in a typed run; otherwise computed here, when the declared
codomain does not say). -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 9): η at `Unit` may read the computed result type; a path on which it is still neutral only keeps the value unnormalised (D59).
def resultIsUnit (fuel : Nat) (fv : Value) (ws : Array Value) (kind : Kind) (B : Option Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if kind == .unit then return true
  if let some B := B then return B == .tUnit
  -- a callee whose Π-type cannot be read is not known to return `Unit`
  let some piTy ← funType? fuel' fv none | return false
  pure ((← resultKind fuel' piTy ws) == .unit)
termination_by structural fuel

/-- [Close]: the call `f(w̄)` has a stuck body; the partial run has been discarded (the
state is back at the call point). `L := let cᵢ = uᵢ`, `C := f(ā)` with `aᵢ = &cᵢ` for
the borrow arguments `wᵢ = borrow_ℓᵢ uᵢ`; the result and the loans follow the table. -/
def closeCall (fuel : Nat) (fv : Value) (ws : Array Value) (kind : Kind) (B : Option Value := none) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  wholeBorrowArgs ws "a call that closes off"
  -- Precondition (v1.1): every argument's content is loan-free (guaranteed by [Access]).
  -- An assertion: a violation is a bug of the rules or of this checker, never a user error.
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
  -- D53: the final read of a sealed program (its `K`) is an observation: it copies, while
  -- the program before it runs with runtime semantics
  let peek (t : Term) : Term := .prim "peek" [t]
  match kind with
  | .ref =>
    let k ← freshLoan
    for ((_, l, _), j) in bs.zipIdx do
      let fill := wrapL (.letIn ⟨"r"⟩ (C 0) (.seq (.assign (.deref (.var 0)) (.val (.loan k))) (peek (cell 1 j))))
      substEnv fuel' (.loan l) (← canonNeutral (.sealed fill)) false
    pure (.borrow k (← canonNeutral (.sealed (wrapL (.letIn ⟨"r"⟩ (C 0) (peek (.place (.deref (.var 0)))))))))
  | _ =>
    for ((_, l, u), j) in bs.zipIdx do
      -- D59 refined: a borrowed place of type `Unit` (its content `()`) is filled with `()`
      let fill ← if u == .unit then pure .unit
        else canonNeutral (.sealed (wrapL (.seq (C 0) (peek (cell 0 j)))))
      substEnv fuel' (.loan l) fill false
    -- D59 refined: the readback at type `Unit` is `()` (η-normal form); the call's effects
    -- are in the fills above
    if ← resultIsUnit fuel' fv ws kind B then return .unit
    canonNeutral (.sealed (wrapL (C 0)))
termination_by structural fuel

-- ### Match: [Match], [Split], stuck blocks

/-- Apply a refinement `σ := r` to Ω, the stored types and the goal ([Split]). -/
def refine (fuel : Nat) (σ : Nat) (r : Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  substEnv fuel' (.abs σ) r true
  modify fun s => { s with refs := (σ, r) :: s.refs }
  if (← get).neutrals.any (·.2 == σ) then renormAll fuel'
termination_by structural fuel

def evalMatch (fuel : Nat) (typed : Bool) (p : Place) (z s : Term) (expected : Option Value := none) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if typed then natScrutinee fuel' p
  accessPath fuel' p
  accessNeutralHead fuel' p
  let v ← matchContent p
  match v with
  | .zero => eval fuel' typed z
  | .succ _ => eval fuel' typed s
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ => if typed then splitThenClose fuel' p z s σ expected else stuckOn v
  | .sealed _ | .loan _ =>
    if !typed then stuckOn v
    else
      let σ ← generalizeNeutral fuel' p v
      let expected ← expected.mapM (substV fuel' v (.abs σ))
      splitThenClose fuel' p z s σ expected
  | _ => err s!"[Match] on a non-Nat value {v}"
termination_by structural fuel

/-- A match's constructors come from its scrutinee's type, never from its patterns: a match
on `Z`/`S` needs a scrutinee whose type normalises to `Nat` (fuzz-port's M2: `x : TG(σ)`,
stuck, was split as a `Nat`, and at `TG(1) = B2` the run met `F`). A type that is stuck is
not known to be `Nat` (fail-safe, as `scrutType` does for inductive matches). -/
def natScrutinee (fuel : Nat) (p : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← placeType fuel' p with
  | .tNat => pure ()
  | T => err s!"[Match] on {← ppPlace p} with `Z`/`S`, but its type {T} is not Nat"
termination_by structural fuel

/-- [Split] on a neutral that is not an abstract value (a sealed program left by an
opaque call, deriver-e346 §E4.3): generalise first, i.e. replace every occurrence of it
(Ω, stored types, goal) by a fresh `σ`, then split on it (v1.2, D22). -/
def generalizeNeutral (fuel : Nat) (p : Place) (n : Value) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- v1.8: σ has the matched place's type
  let T ← placeType fuel' p
  let σ ← freshAbs T
  trace fun _ => s!"[Split] generalise {n} to σ{σ} : {T}"
  substEnv fuel' n (.abs σ) true
  modify fun s => { s with neutrals := (n, σ) :: s.neutrals }
  pure σ
termination_by structural fuel

/-- The type of a sealed program in result form, from its head's declared codomain: as it
stands when it is closed, and otherwise at the call's arguments, when every parameter it
mentions is given a value (a generic function's `Opt(V)` at the `V` it was called with; the
call was checked against the parameter types when it was made). -/
def sealedResultType? (fuel : Nat) (t : Term) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let rec body : Term → Term
    | .letIn _ _ u => body u
    | u => u
  match body t with
  | .call (.val f) as true =>
    match f with
    | .gfn n => match (← lookupGlobal n).ty with
      | .tPi cs (.pi hs ds c) =>
        if c.freeVars.isEmpty then pure (some (← evalType fuel' c)) else
        let np := ds.length
        let ws : Array (Option Value) := (as.map fun | .val v => some v | _ => none).toArray
        unless cs.isEmpty && ws.size == np && c.freeVars.all (fun j => j < np && (ws[np - 1 - j]!).isSome) do
          return none
        onCopy do
          pushFrame
          for (h, w) in hs.zip ws.toList do pushBind h none (w.getD .bot)
          some <$> evalType fuel' c
      | _ => pure none
    | _ => pure none
  | _ => pure none
termination_by structural fuel

/-- Re-normalise every sealed program in the state (after a generalised neutral has been
refined, sealed programs whose runs derive it may now make progress). -/
def renormAll (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for p in allPos (← get).env do
    setAt p (← renormV fuel' (← getAt p))
  -- types re-normalise as types: erased, reads copy (D53)
  if let some g := (← get).goal then
    let g' ← withErased (renormV fuel' g)
    modify fun s => { s with goal := some g' }
  let f := (← get).env.size
  for fi in [0:f] do
    let n := (← get).env[fi]!.binds.size
    for i in [0:n] do
      if let some T := (← get).env[fi]!.binds[i]!.ty then
        let T' ← withErased (renormV fuel' T)
        modifyFrame fi fun fr => { fr with binds := fr.binds.modify i ({ · with ty := some T' }) }
termination_by structural fuel

def renormV (fuel : Nat) (v : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !(v.anyAtom fun | .sealed _ => true | _ => false) then return v
  match v with
  | .sealed t => do
    let t' ← renormT fuel' t
    canonNeutral (← nfSealed fuel' t')
  | .succ w => return .succ (← renormV fuel' w)
  | .borrow l w => return .borrow l (← renormV fuel' w)
  | .ind ty c h ps fs => return .ind ty c h (← ps.mapM (renormV fuel')) (← fs.mapM (renormV fuel'))
  | .tEq A a b => mkEqM fuel' (← renormV fuel' A) (← renormV fuel' a) (← renormV fuel' b)
  | .tInd n as => return .tInd n (← as.mapM (renormV fuel'))
  | .tRef A => return .tRef (← renormV fuel' A)
  -- closures and Π-types too: their captures and embedded values (arrays-library: a goal
  -- `… ∧ Π(…). …` whose Π captured a sealed program stayed stale after a split)
  | .clo cs t => return .clo (← cs.mapM (renormV fuel')) (← renormT fuel' t)
  | .tPi cs t => return .tPi (← cs.mapM (renormV fuel')) (← renormT fuel' t)
  | _ => return v
termination_by structural fuel

/-- Re-normalise the values embedded in a term (the sealed programs among them), everywhere
`substT` substitutes. -/
def renormT (fuel : Nat) (t : Term) : M Term := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !(t.anyAtom fun | .sealed _ => true | _ => false) then return t
  let go := renormT fuel'
  match t with
  | .val v => return .val (← renormV fuel' v)
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
termination_by structural fuel

/-- [Split] for a non-tail match: check each arm under its refinement, then close the
match off as a stuck block and continue once from the unrefined state (D15). The
block's type is the arms' common type, or the annotation `let x : T = match …`
(each arm is then checked against `T` refined, v1.2 D22). -/
def splitThenClose (fuel : Nat) (p : Place) (z s : Term) (σ : Nat) (expected : Option Value) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  splitArmsThenClose fuel' (Term.matchNat p z s) σ
    [(pure .zero, z), (do pure (.succ (.abs (← freshAbs .tNat))), s)] expected
termination_by structural fuel

/-- The general form: one arm per constructor, each checked under the refinement its
builder produces (fresh abstract values for the fields), then close off (`closeBlock`, which
runs the arms). -/
def splitArmsThenClose (fuel : Nat) (mt : Term) (σ : Nat) (arms : List (M Value × Term))
    (expected : Option Value) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let blockArms := arms.map fun (mk, arm) => BlockArm.mk
    (do let r ← mk; refine fuel' σ r; pure r)
    (fun r => do
      let (av, T) ← eval fuel' true arm
      let fl ← getFlags
      let some T := T | err "internal: untyped arm"
      if let some E := expected then
        let E' ← substV fuel' (.abs σ) r E
        unless ← conv fuel' T E' do
          err s!"an arm of the annotated match has type {T}, but the annotation refined to this arm is {E'}"
      setFlags fl
      pure (av, T))
  closeBlock fuel' mt blockArms expected
termination_by structural fuel

/-- The refinement of `σ` to constructor `c` of an inductive type at parameters `ps`:
fresh abstract values for its fields, of the fields' types; a field that is a proof
gets `⋆` (as a proof parameter does, D27). -/
def ctorRefinement (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (cn, _) := d.ctors[c]!
  -- D64: each field's type from the earlier fields' fresh values (`σ₂ : T₂[σ₁]`)
  let fs := (← fieldsGeneric fuel' d ps c).map (·.2.2)
  pure (.ind d.name c ⟨cn⟩ ps fs)
termination_by structural fuel

/-- The inductive type of a matched place and its parameters, from the place's type (the
arms' constructors name `ty`; `""` for a match with no arms). The type is read, not
assumed from the arms (finding: v1.9's checker split a `T(n)`-typed place with `L`'s
constructors, so `f(1, x)`, with `T(1) = Nat`, ran `L`'s arms on a number). -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 12): the scrutinee's stored type as refined; refinement changes its parameters, never its head, and a neutral type is a type error (note 25).
def scrutType (fuel : Nat) (p : Place) (ty : String) : M (IndDecl × List Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← placeType fuel' p with
  | .tInd n ps =>
    if ty != "" && n != ty then err s!"[Match] on {← ppPlace p} : {Value.tInd n ps}, with the constructors of {ty}"
    pure (← lookupInd n, ps)
  | T => err s!"[Match] on {← ppPlace p}, whose type {T} is not an inductive type{if ty == "And" then " (And(True, P) ≡ P: match on the conjunct instead)" else ""}"
termination_by structural fuel

/-- D45 (v2.0): a match on a proof (the arms' constructors are those of a Prop inductive),
or with no arms, is by the scrutinee's *type*: its content (`⋆`, or an abstract value) is
never inspected, so the decision is the same on every path. No constructors: no arms, any
result type (the annotation's), erased and unreachable (its value is `⋆`). One: its arm,
the fields being places holding `⋆`. Several: each arm is checked and each must be a proof,
so the match is a proof, `⋆` (it cannot pick an arm). Subsingleton elimination: unless
the type has no constructors or one whose fields are all propositions, every arm must be
a proof (the declared reading of "its result is a proposition", D42). -/
def evalMatchByType (fuel : Nat) (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term))
    (expected : Option Value) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  accessPath fuel' p
  let v ← matchContent p
  if v == .bot then err s!"[Match] on {← ppPlace p}, which was moved out"
  if arms.isEmpty then
    if typed then
      let (d, _) ← scrutType fuel' p ty
      unless d.ctors.isEmpty do err s!"a match with no arms on {← ppPlace p} : {d.name}, which has constructors"
      if expected.isNone then err "annotate a match with no arms outside tail position (let x : T = match p {})"
    -- D58: reached, it is unreachable in a closed run. In a proof position it is erased
    -- (⋆); anywhere else it is stuck, closed off like a match on an abstract value, never
    -- a value of the wrong type
    if !typed then stuckNow
    let B := expected.get!
    unless ← isPropV fuel' B do return ← closeBlock fuel' (.matchInd p ty arms) [] (some B)
    setFlags (true, true)
    return (.proof, expected)
  let d ← lookupInd ty
  let ps ← if typed then (·.2) <$> scrutType fuel' p ty else pure []
  let large ← largeElim d
  let needProof := typed && !large
  let subErr : M Unit := err (subsingletonMsg d)
  -- a constructor value (not reached: a Prop inductive's constructor values are `⋆`, D42)
  if let .ind _ c _ _ _ := v then
    match arms[c]? with
    | some (_, a) => return ← eval fuel' typed a
    | none => err s!"[Match] no arm for constructor {c}"
  -- D49 (2): a match on a proof of a non-subsingleton is erased (its checked arms are all
  -- proofs), so a run does not run it: its value is ⋆ (read from the declaration)
  if !typed && !large then
    setFlags (true, true)
    return (.proof, none)
  if let [(_, a)] := arms then
    let a ← if typed then bindDataFields fuel' p d ps 0 a else pure a
    let r ← eval fuel' typed a
    if needProof && !(← getFlags).2 then subErr
    return r
  if !typed then
    -- not reached by checked programs (a subsingleton has at most one constructor): an
    -- erased match is ⋆, otherwise no arm can be chosen and the match is stuck
    let saved ← get
    discard (eval fuel' false arms[0]!.2)
    let pf := (← getFlags).2
    restoreArm saved
    if pf then setFlags (true, true); return (.proof, none)
    stuckNow
  let saved ← get
  let mut tys := #[]
  let mut allProof := true
  for ((_, a0), c) in arms.zipIdx do
    let a ← bindDataFields fuel' p d ps c a0
    let (_, T) ← eval fuel' true a
    allProof := allProof && (← getFlags).2
    let some T := T | err "internal: untyped arm"
    if let some E := expected then
      unless ← conv fuel' T E do err s!"an arm of the annotated match has type {T}, but the annotation is {E}"
    tys := tys.push T
    restoreArm saved
  let B ← match expected with
    | some E => pure E
    | none =>
      let T0 := tys[0]!
      for T in tys do
        unless ← conv fuel' T T0 do err s!"the arms of a match on a proof have different types ({T0} and {T}); annotate it"
      pure T0
  if !allProof then subErr
  setFlags (true, true)
  pure (.proof, some B)
termination_by structural fuel

/-- [Match] / [Split] on a declared inductive type. -/
def evalMatchInd (fuel : Nat) (typed : Bool) (p : Place) (ty : String) (arms : List (Hint × Term))
    (expected : Option Value := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  abstractMatchCheck p ty
  if ← byTypeMatch ty arms then return ← evalMatchByType fuel' typed p ty arms expected
  accessPath fuel' p
  accessNeutralHead fuel' p
  let v ← matchContent p
  match v with
  | .ind t c _ _ _ =>
    if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
    if typed then discard (scrutType fuel' p ty)
    match arms[c]? with
    | some (_, a) => eval fuel' typed a
    | none => err s!"[Match] no arm for constructor {c}"
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ =>
    if !typed then stuckOn v
    else
      let (d, ps) ← scrutType fuel' p ty
      splitArmsThenClose fuel' (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement fuel' d ps c, a)) expected
  | .sealed _ | .loan _ =>
    if !typed then stuckOn v
    else
      let (d, ps) ← scrutType fuel' p ty
      let σ ← generalizeNeutral fuel' p v
      let expected ← expected.mapM (substV fuel' v (.abs σ))
      splitArmsThenClose fuel' (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement fuel' d ps c, a)) expected
  | _ => err s!"[Match] on {v}, which is not a value of {ty}"
termination_by structural fuel

/-- D53: a place an arm moved out, as it exists in the closed-off (unrefined) state. The
arm's refinement may have exposed it (`q0.1` of an abstract pair, `n0`'s predecessor):
through a value of a single-constructor type the abstract value is refined to that
constructor, a total refinement (as a split with one arm); through any other, the move is
of the longest prefix that exists, since some arm moves a part of it (fuzz-port M1). -/
def movedPlace (fuel : Nat) (q : Place) : M Place := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if (← content? q).isSome then return q
  let parent : Place → Option Place
    | .deref p | .fst p | .snd p | .field _ p => some p
    | .var _ => none
  let some p := parent q | return q
  let p ← movedPlace fuel' p
  match ← content p with
  | .abs σ =>
    match ← absType σ with
    | .tInd n ps =>
      let d ← lookupInd n
      if d.ctors.length == 1 then
        -- D68: the same fields in every private copy (a statement's sides each move out of `σ`)
        let r ← match (← get).etaRefs.lookup σ with
          | some r => pure r
          | none => do
            let r ← ctorRefinement fuel' d ps 0
            modify fun s => { s with etaRefs := (σ, r) :: s.etaRefs }
            pure r
        refine fuel' σ r
        movedPlace fuel' q
      else pure p
    | _ => pure p
  | _ => pure p
termination_by structural fuel

/-- [Block], the one place a stuck block is formed (D76). A stuck match ([Split]), a `J` whose
endpoints are not convertible ([T-J-stuck]) and a zero-arm match outside a proof position are
closed off here, as a call to an anonymous function of their free places. The block runs its
arms itself (`BlockArm`): each from the unrefined state, under its own setup, and each is checked
to its return by `bodyReturns`, the check every function body's return goes through. So a block
cannot be formed without its arms having been checked whole where its borrows end: the
producer obligation for the sealed programs a block leaves, of which D72 (a match's arms) and
D75 (a `J`'s transported term) were two instances found missing.

The places are captured as Rust infers closure captures, on maximal place prefixes: a place
some arm moves out of is moved in; otherwise a place written or borrowed (under `&_` or left of
`:=`) in some arm is passed as `&`; otherwise a place read is copied. A borrow variable read as a
whole is a move (reading a borrow moves it); assigning a borrow variable as a whole moves it too
(passing `&x` would be `&&T`). The block's type is `B?`, or else its arms' common type. -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 13): captures read copy-ness, the places an arm leaves ⊥, and a split capture's constructor; each is type-directed or survives refinement.
def closeBlock (fuel : Nat) (mt : Term) (arms : List BlockArm) (B? : Option Value) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let saved ← get
  let f0 := (← get).env.size - 1
  let n0 := (← get).env[f0]!.binds.size
  let mut tys : Array Value := #[]
  let mut armMovedAll : List Place := []
  -- v1.7 (D35): the block is erased exactly when its match would be, when every arm is a proof
  -- (a block with no arms runs nothing and is not erased)
  let mut allProof := !arms.isEmpty
  -- each arm's end state, result and type: where the block returns (`bodyReturns`, below)
  let mut ends : Array (MState × Value × Value) := #[]
  for arm in arms do
    let r ← arm.setup
    let ls := (← get).placeLog.size
    let (av, T) ← arm.body r
    allProof := allProof && (← getFlags).2
    -- the arm's effect on the places it captures, read from its log of moves and
    -- assignments (D53: by place, at the granularity of the move, `q1.1`; an inner block's
    -- moves are its arguments', so they compose; fuzz-port M1, N1)
    let armMoved ← armMoves ((← get).placeLog.extract ls (← get).placeLog.size) f0 n0
    for q in armMoved do
      unless armMovedAll.any (placeEq · q) do armMovedAll := armMovedAll ++ [q]
    -- the arm's result is held as a temporary there, so that a borrow it returns into a
    -- lent place is still in Ω when that place is checked
    pushTemp av
    ends := ends.push ((← get), av, T)
    restoreArm saved
    tys := tys.push T
  let B ← match B? with
    | some E => pure E
    | none =>
      let some T0 := tys[0]? | err "internal: a match with no arms"
      for T in tys do
        unless ← conv fuel' T T0 do
          err s!"the arms of a non-tail match have different types ({T0} and {T}); annotate it (let x : T = match …)"
      pure T0
  -- D68: a closure or Π-type in an arm captures by move what it mentions (unless a copy), in a
  -- statement too, whether or not the run took that arm: the block takes the place by move on
  -- every path (fuzz case 14942: the abstract run's inner block moved it, the ground run's did
  -- not, and only the ground run found the closure capturing a borrowed place)
  let moved ← do
    let mut mv := armMovedAll
    for (o, p) in mt.fnOccs 0 do
      let q := p.mapRoot fun _ => .var o
      -- a place whose type cannot be read is not known to be a copy: the block moves it
      let copy ← match ← placeType? fuel' q with
        | some T => isCopyType fuel' T
        | none => pure false
      unless copy do
        unless mv.any (placeEq · q) do mv := mv ++ [q]
    pure mv
  let moved ← moved.foldlM (fun acc q => do
      let q' ← movedPlace fuel' q
      pure (if acc.contains q' then acc else acc ++ [q'])) []
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
  -- the free places used, re-rooted at the frame index, with their capture mode
  -- (0 = copy, 1 = &, 2 = move)
  let mut uses : Array (Place × Nat) := #[]
  let mut wholeUses : Array (Place × PKind) := #[]   -- D53: how each place is used as a whole
  for (o, p, k) in mt.freeOccsBlock do
    let q := p.mapRoot fun _ => .var o
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
  -- a proof is never taken by `&` (D66: its type is a proposition, not in Type₀): its value is `⋆`, so an
  -- arm's write through a pattern variable of a matched proof (a field, a fresh value by
  -- D49 (3), in a proof position by D45) is local to the block's own copy (R8, fuzz-port)
  caps ← caps.mapM fun (q, k) => do
    if k != 1 then return (q, k)
    let isProof ← match ← placeType? fuel' q with
      | some T => isPropV fuel' T
      | none => pure false
    pure (if isProof then (q, 0) else (q, k))
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
        let d ← lookupInd t
        let names := (d.ctors[c]?.map (·.2.map (·.1))).getD []
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
  -- [Fix] captures no borrow (D63, rule-audit item 7): a closure or Π-type in an arm that
  -- mentions a place the block takes by `&` would capture the block's borrow parameter when
  -- the block re-runs, so the block is rejected where it is formed, alike on every path
  -- (fuzz-port, seed 1, case 182: it failed only at re-normalisation)
  for (o, p) in mt.fnOccs 0 do
    let q := p.mapRoot fun _ => .var o
    if caps.any (fun (c, k) => k == 1 && placePrefix c q) then
      err s!"a closure or Π-type in an arm of a stuck match captures {← ppPlace q}, which the block takes by borrow (closures capture no borrows, RULES §1)"
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
  -- [Return] at each arm's end (D76): the block is an anonymous function, so each arm ends
  -- where the function returns, and `bodyReturns` checks there what every function body's
  -- return is checked for. A place the block takes by borrow is its borrow parameter, whose
  -- borrow ends at the return; a borrow variable it moves in whole is ended by its frame
  -- there too. So each such place must be of its type again in the state the arm ends in, and
  -- so must the arm's result. Without this an arm's lie about a dependent field is never
  -- re-checked: the block closes off, the place receives a sealed program that the generic
  -- path treats as whole, and the direct path, which runs the arm and checks nothing
  -- ([Repack] is not checked on instances), is left with a value of the wrong type
  -- (`StuckBlocks.LieSeq`, D72; `JBlocks.JLie`, D75).
  for (e, av, T) in ends do
    let cur ← get
    onFail (do
      set e
      let fe ← topIdx
      let nbe := (← get).env[fe]!.binds.size
      unless nbe == nb do err "internal: an arm of a stuck match ended in a different frame shape"
      let mut lent : List Place := []
      for (q, mode) in capsS do
        let isLent ← match mode, q with
          | 1, _ => pure true
          | 2, .var o =>
            let b := (← get).env[fe]!.binds[nbe - 1 - o]!
            pure (b.val.isBorrow || (b.ty matches some (.tRef _)))
          | _, _ => pure false
        if isLent then lent := lent ++ [q]
      bodyReturns fuel' "a stuck match's arm returns it" av T lent "lent to a stuck match, whose arm returns with it")
      (set cur)
    set cur
  let n := capsS.size
  let mut hints := #[]
  let mut doms := #[]
  let mut args := #[]
  let mut pflags := #[]
  for (q, mode) in capsS do
    let T ← placeType fuel' q
    repackAt fuel' q T "captured whole by a stuck match"
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
      doms := doms.push T; args := args.push (Term.place q)
    | 1 =>
      -- D66: the block borrows the place, so its type must be known to be in Type₀ (a stuck
      -- type `⌈T(σ)⌉` by its head's declared codomain: reviewer-6's A12)
      if !(← isBorrowable fuel' T) then
        err s!"[D66] a stuck match would borrow {← ppPlace q}, whose type {T} is not known to be in Type₀"
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
  let (v, _) ← evalCall fuel' false (.val anon) args.toList false (some (if allProof then 2 else 0))
  pure (v, some B)
termination_by structural fuel

-- ### Observation and `Id` (RULES §4)

/-- `⟦t⟧^W`: on a private copy of Ω, run `t`, end every borrow, and return the result
and the final contents of the owners in `W` (a tuple of the machine, not a `Pair` value,
D52). -/
def observe (fuel : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos) : M (Value × List Value) := onCopy do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (v, T) ← eval fuel' typed t A      -- A: a hint for a constructor's parameters
  expectTy fuel' "a side of Id" T A
  pushTemp v
  modify fun s => { s with observing := true }
  endAll fuel'
  modify fun s => { s with observing := false }
  let v ← popTemp
  let ws ← W.mapM getAt
  pure (v, ws)
termination_by structural fuel

/-- [Obs] is stated with the typing judgement wherever `Id` is evaluated (D63, rule-audit item
9). In an untyped run (a callee's body, a sealed program's re-run) the side runs in the
machine, which computes the same value as typing whenever it is not stuck; if it is stuck, it
is observed again with the typing judgement, so its stuck match is split and closed off as a
block, as when the same `Id` is formed directly. (Typing from the start would need the type of
every value in an untyped frame, which `⋆` and `⊥` do not have.) -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 21): re-observation when stuck; refinement only removes stuckness, and when not stuck the machine and typing compute the same value.
def observeTyping (fuel : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos) : M (Value × List Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if typed then return ← observe fuel' typed t A W
  catchStuck (observe fuel' false t A W) fun _ => observe fuel' true t A W
termination_by structural fuel

/-- `Id A t u ≡ And(Eq A r r', And(Eq T₁ w₁ w'₁, …))` over the result and the owners in
`W = W(t, u)` (just `Eq A r r'` when `W` is empty), both sides from the same Ω on
independent copies (v2.1, D52: directly, not through a pair, so `A` may be any borrow-free
type, a proposition or a universe included). -/
def idType (fuel : Nat) (typed : Bool) (A t u : Term) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let A' ← evalType fuel' A
  if A'.typeHasRef then err s!"Id at {A'}: A must be borrow-free (RULES §4)"
  let st ← get
  let W := footprint st.env [t, u]
  let (a, as) ← observeTyping fuel' typed t A' W
  let (b, bs) ← observeTyping fuel' typed u A' W
  -- an owner's type: its binding's, else its content's. An untyped owner that is lent out
  -- now (a sealed program's re-run binding a cell that a returned borrow still holds: R1's
  -- residual) is typed by what the observation read from it, once every borrow had ended
  let Ts ← W.zipIdx.mapM fun (p, i) => do
    match ← tyAt p with
    | some T => pure T
    | none =>
      match ← [← getAt p, as[i]!, bs[i]!].findSomeM? (valType? fuel') with
      | some T => pure T
      | none =>
        -- D68: an owner both sides consumed has no type to read; its equation is stuck
        if as[i]!.hasHole || bs[i]!.hasHole then pure .tUnit
        else err s!"cannot infer the type of the value {← getAt p}"
  -- D64 [Repack]: `Id` observes its result and owners whole
  if typed then
    for (T, (x, y)) in (A', (a, b)) :: Ts.zip (as.zip bs) do
      repackCheck fuel' "Id observes it" x T
      repackCheck fuel' "Id observes it" y T
  let eqs ← ((A', (a, b)) :: Ts.zip (as.zip bs)).mapM fun (T, (x, y)) => mkEqM fuel' T x y
  pure (andList eqs)
termination_by structural fuel

-- ### Typing: [Def], [Split] in tail position

/-- D61: the neutral that a run of the sealed program `t` is stuck on: re-run `t` as [Seal]
does and report the content of the scrutinee of the match it stopped at, if any. -/
def stuckScrutinee (fuel : Nat) (t : Term) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let saved ← get
  modify fun s => { s with env := #[{}], depth := s.depth + 1 }
  -- a re-run that errors is an error (as [Seal-err] makes it), not "stuck on nothing"
  let r ← catchStuck (do discard (withErased (eval fuel' false t)); pure none) fun on => pure on
  restoreKeep saved
  pure r
termination_by structural fuel

/-- D61 `split f`: find the neutral to split. Walk the goal's sealed programs in pre-order,
left to right; from each, follow the chain of scrutinees its run is stuck on (each link
the content of the scrutinee of the match the previous one stopped at) while they are
sealed programs; the first sealed scrutinee whose head call is `f` is the one. A link may
also be an abstract value that stands for a sealed program generalised earlier (a D34
record, which re-derivations of the program are replaced by): if that program's head
call is `f`, it is the one, already generalised. -/
def findSplit (fuel : Nat) (f : String) (G : Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for t in sealedIn G do
    let mut cur := t
    for _ in [0:64] do
      match ← stuckScrutinee fuel' cur with
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
termination_by structural fuel

/-- D61: generalise a neutral found in the goal to a fresh `σ` of type `T`, as [Split] does
for a sealed scrutinee (D34, D37), and return `σ`. -/
def generalizeFound (fuel : Nat) (n : Value) (T : Value) : M Nat := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let σ ← freshAbs T
  trace fun _ => s!"[Split] generalise {n} to σ{σ} : {T}"
  substEnv fuel' n (.abs σ) true
  modify fun s => { s with neutrals := (n, σ) :: s.neutrals }
  pure σ
termination_by structural fuel

/-- D61: the neutral `split f` splits and its type, or an error. -/
def splitTarget (fuel : Nat) (f : String) : M (Nat × Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some G := (← get).goal | err "split: no goal"
  let some n := ← findSplit fuel' f G
    | err s!"split {f}: the goal {G} is not stuck on the result of a call of {f}"
  if let .abs σ := n then return (σ, ← absType σ)     -- generalised already
  let .sealed t := n | err "internal: split target"
  let some T := ← sealedResultType? fuel' t
    | err s!"split {f}: the type of {n} is not known (its head's result type depends on the arguments)"
  pure (← generalizeFound fuel' n T, T)
termination_by structural fuel

/-- Check a term in tail position. At the end of every path, `k` gets the result and
its type (in that path's refined state). A match on an abstract `σ` here is split:
each arm is checked to the end under its refinement ([Split]). -/
def checkTail (fuel : Nat) (t : Term) (k : Value → Value → M Unit) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- the editor: an error here (`k`'s included) is reported at `t`, and hovering `t` shows its goal
  locatedTail t (checkTailAt fuel' t k)
termination_by structural fuel

def checkTailAt (fuel : Nat) (t : Term) (k : Value → Value → M Unit) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match t with
  | .prim "split" [.const f, u] =>
    -- D61: `split f in u`: split the goal's stuck result of `f`, `u` in every arm
    let (σ, T) ← splitTarget fuel' f
    let saved ← get
    match T with
    | .tNat =>
      refine fuel' σ .zero
      trace fun _ => s!"[Split] σ{σ} := 0"
      checkTail fuel' u k
      restoreArm saved
      let σ' ← freshAbs .tNat
      refine fuel' σ (.succ (.abs σ'))
      trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
      checkTail fuel' u k
      restoreArm saved
    | .tInd n ps =>
      let d ← lookupInd n
      for c in List.range d.ctors.length do
        let r ← ctorRefinement fuel' d ps c
        refine fuel' σ r
        trace fun _ => s!"[Split] σ{σ} := {r}"
        checkTail fuel' u k
        restoreArm saved
    | _ => err s!"split {f}: its result type {T} is not an inductive type"
  | .prim "splitArms" [.const f, .letIn h _ w] =>
    -- D61: `split f { C(x̄) => u, … }`: the split value is bound to a hidden variable, and
    -- the arms are an ordinary match on it
    let (σ, T) ← splitTarget fuel' f
    pushBind h (some T) (.abs σ) false
    checkTail fuel' w fun r R => do
      let fl ← getFlags
      pushTemp r
      dropTopBind fuel'
      setFlags fl
      k (← popTemp) R
  | .prim "rewrite" [h, u] | .prim "rewriteR" [h, u] =>
    -- D60: in tail position the rewritten goal becomes the path's goal, so `u` may split
    let some G := (← get).goal | err "rewrite: no goal"
    let G' ← rewriteGoal fuel' (t matches .prim "rewriteR" _) h G
    modify fun s => { s with goal := some G' }
    checkTail fuel' u k
  | .letIn h u w =>
    let du ← withLive true (declOf fuel' false [] [] u)
    let (v, T) ← eval fuel' true u
    pushBind h T v (← getFlags).2 (← refineDecl fuel' du T v)
    checkTail fuel' w fun r R => do
      let fl ← getFlags      -- the path's tail flags (dropping may normalise)
      pushTemp r
      dropTopBind fuel'
      setFlags fl
      k (← popTemp) R
  | .seq u w =>
    let (v, _) ← eval fuel' true u
    dropValue fuel' v
    checkTail fuel' w k
  | .matchNat p z s =>
    natScrutinee fuel' p
    accessPath fuel' p
    accessNeutralHead fuel' p
    match ← matchContent p with
    | .zero => checkTail fuel' z k
    | .succ _ => checkTail fuel' s k
    | .abs σ =>
      let saved ← get
      refine fuel' σ .zero
      trace fun _ => s!"[Split] σ{σ} := 0"
      checkTail fuel' z k
      restoreArm saved
      let σ' ← freshAbs .tNat
      refine fuel' σ (.succ (.abs σ'))
      trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
      checkTail fuel' s k
      restoreArm saved
    | v@(.sealed _) | v@(.loan _) =>
      discard (generalizeNeutral fuel' p v)
      checkTail fuel' t k
    | _ =>
      let (v, T) ← eval fuel' true t
      k v T.get!
  | .matchInd p ty arms =>
    abstractMatchCheck p ty
    if ← byTypeMatch ty arms then
      -- D45 (v2.0): [Split] on a proof is by its type: each arm is checked, with the fields
      -- as places holding ⋆ and no refinement; no arms, no paths
      accessPath fuel' p
      let v ← matchContent p
      if v == .bot then err s!"[Match] on {← ppPlace p}, which was moved out"
      let (d, ps) ← scrutType fuel' p ty
      if arms.isEmpty && !d.ctors.isEmpty then
        err s!"a match with no arms on {← ppPlace p} : {d.name}, which has constructors"
      let needProof := !(← largeElim d)
      let k' : Value → Value → M Unit := fun r R => do
        if needProof && !(← getFlags).2 then err (subsingletonMsg d)
        k r R
      match v with
      | .ind _ c _ _ _ => checkTail fuel' (arms[c]!).2 k'     -- not reached: a Prop inductive's values are `⋆` (D42)
      | _ =>
        let saved ← get
        for ((_, a), c) in arms.zipIdx do
          checkTail fuel' (← bindDataFields fuel' p d ps c a) k'     -- D49 (3)
          restoreArm saved
      return
    accessPath fuel' p
    accessNeutralHead fuel' p
    match ← matchContent p with
    | .ind t c _ _ _ =>
      if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
      discard (scrutType fuel' p ty)
      match arms[c]? with
      | some (_, a) => checkTail fuel' a k
      | none => err s!"[Match] no arm for constructor {c}"
    | .abs σ =>
      let (d, ps) ← scrutType fuel' p ty
      let saved ← get
      for (c, (_, a)) in (List.range d.ctors.length).zip arms do
        let r ← ctorRefinement fuel' d ps c
        refine fuel' σ r
        trace fun _ => s!"[Split] σ{σ} := {r}"
        checkTail fuel' a k
        restoreArm saved
    | v@(.sealed _) | v@(.loan _) =>
      discard (generalizeNeutral fuel' p v)
      checkTail fuel' t k
    | _ =>
      let (v, T) ← eval fuel' true t
      k v T.get!
  | _ =>
    let (v, T) ← eval fuel' true t (← get).goal     -- the goal: a hint for a constructor's parameters
    match T with
    | some T => k v T
    | none => err "internal: untyped result in the checker"
termination_by structural fuel

/-- [Def]: `fix f (x̄:Ā):B := b` is checked at its generic call. Ω has a fresh owned
place `cᵢ ↦ σᵢ` for each borrow parameter `xᵢ : &Tᵢ` (frame 0); the call is
`f(ā)` with `aᵢ = &cᵢ` or `σᵢ`; the goal is the [Call-type] of that call; the body
runs in a pushed frame and its result's type must convert to the goal as refined by
splits. Afterwards the whole state is restored. -/
def checkFix (fuel : Nat) (fv : Value) (cs : List Value) (t : Term) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .fix self hs ds c dec body := t | err "internal: not a fix"
  borrowParamCheck ds c
  let saved ← get
  -- the body is the checked program (D64: its [Repack] points are checked, and the borrow
  -- parameters' borrows end with their values repacked when the frame pops)
  modify fun s => { s with typing := true }
  -- D31 (v1.5): without `by`, f is not in scope in its body (a λ)
  if dec.isNone && (body.freeOccs.any (·.1 == ds.length)) then
    err s!"{self.name} is not in scope in its own body: it declares no decreasing parameter (`by x`), so it is not recursive (D31)"
  let n := ds.length
  unless headOnly (fun d p => p.root == d + n) 0 body do
    err s!"[Rec] {self.name} occurs in its own body other than as the head of a call (fix L1)"
  -- keep `refs` (refinements made on the way to a nested fix still hold) and the
  -- enclosing functions' [Rec] contexts
  modify fun s => { s with env := #[{}], goal := none }
  let pf ← paramFlags fuel' cs ds
  let (pds, cd) ← paramDecls fuel' cs hs ds c
  pushFrame
  pushCaps fuel' cs
  let mut entries := #[]
  for (((d, h), p), pd) in ((ds.zip hs).zip pf).zip pds do
    let A ← evalType fuel' d
    match A with
    | .tRef T =>
      let c ← absOf T
      let l ← freshLoan
      modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
      pushBind h (some A) (.borrow l c) p pd
      entries := entries.push (match c with
        | .abs σ => if T == .tNat || (T matches .tInd ..) then some σ else none
        | _ => none)
    | _ =>
      if ← isPropV fuel' A then
        pushBind h (some A) .proof p (← refineDecl fuel' pd (some A) .proof)
        entries := entries.push none
      else
        let c ← absOf A
        pushBind h (some A) c p (← refineDecl fuel' pd (some A) c)
        entries := entries.push (match c with
          | .abs σ => if A == .tNat || (A matches .tInd ..) then some σ else none
          | _ => none)
  let goal ← evalType fuel' c
  trace fun _ => s!"[Def] {self.name}: goal {goal}"
  let F1 ← popFrameRaw
  let piTy := Value.tPi cs (.pi hs ds c)
  pushFrame
  pushCaps fuel' cs
  pushBind self (some piTy) fv false (.pi cd)
  for b in F1.binds.extract cs.length F1.binds.size do pushBind b.hint b.ty b.val b.proof b.decl
  -- [Rec]: the decreasing parameter is the one named by `by xⱼ` (v1.2, D23); without
  -- `by` the function is not recursive (no candidate survives a recursive call)
  let cands ← match dec with
    | some j =>
      if (entries[j]?.join).isNone then
        err s!"`by {(hs.getD j ⟨"?"⟩).name}`: the decreasing parameter must have an inductive type (or be a borrow of one)"
      pure [j]
    | none => pure []
  let fr : RecCtx := { fn := fv, entries, cands, uid := (← get).nextRecUid }
  modify fun s => { s with nextRecUid := s.nextRecUid + 1 }
  modify fun s => { s with goal := some goal, recStack := fr :: s.recStack }
  -- D53 (b): the body of a function whose calls are erased is an erased term
  -- (tracked with or without D53: K2/K3 read it too)
  let bodyCopies ← pure ((← fnClass fuel' piTy) != 0)
  withErasedIf bodyCopies <| checkTail fuel' body fun v T => do
    wholeReturned v
    bodyReturns fuel' s!"{self.name} returns it" v T [] ""
    pushTempAt ((← topIdx) - 1) v
    popFrame fuel'
    discard popTemp
    let g := (← get).goal.getD .bot
    trace fun _ => s!"[Def] {self.name}: path ends with type {T} against goal {g}"
    unless ← conv fuel' T g do
      err s!"the body of {self.name} has type {T}, but the goal is {g}"
  restoreKeep saved
termination_by structural fuel

end

/-- Push parameters with their declared-type readings (the earlier ones in scope). -/
def paramDecl (d : Term) : M DeclInfo := do withLive true (typeDecl (← fuelLeft) false [] [] d)

end Ochr
