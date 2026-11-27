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

/-- D102: a proper prefix of `p` holds `⋆`, so `p` is a part of a proof, which has no value of its
own (a total query, like `content?`). -/
def underProof : Place → M Bool
  | .var _ => pure false
  | .deref q | .proj _ q | .field _ q => do
    if (← content? q) == some .proof then pure true else underProof q

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
  -- static ends: a place lent to a returned borrow is on the path of every access below it
  | .gloan l w, ss => if liveLoan env l then some l else firstLiveLoanOnPath env w ss
  -- static ends: a place below a sealed program (a stuck call's fill) lies at an unknown position
  -- inside it, so the program's holes are on its path (as for matching, D29), as a mark is
  | v@(.sealed _), _ :: _ => (liveLoansIn env v).head?
  | v, s :: ss => (stepV s v).bind (firstLiveLoanOnPath env · ss)
  | _, [] => none
termination_by v ss => (ss, v)

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
  | .succ t | .ref t => headOnly isSelf c t
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
  | .assign _ t | .succ t | .ref t => constHeadOnly n t
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

/-- The field steps of a place, each with the place it is a field of (innermost first): what a
write or borrow through the place passes through ([Open], `openWrite`). -/
def Place.fieldPrefixes : Place → List (Place × FieldRef)
  | .field g q => (q, g) :: Place.fieldPrefixes q
  | .deref q | .proj _ q => Place.fieldPrefixes q
  | .var _ => []

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

/-- D81: the place a term reads, borrows or assigns, and the term as a function of it. -/
def Term.placeOperand? : Term → Option (Place × (Place → Term))
  | .place p => some (p, .place)
  | .borrow p => some (p, .borrow)
  | .assign p u => some (p, (.assign · u))
  | _ => none

/-- One step added to a place. -/
def stepPlace (q : Place) : Step → Place
  | .deref => .deref q | .proj i => .proj i q | .field g => .field g q

mutual
/-- D84: the places under `q` whose content in its value `v` is `⊥` (moved out). -/
def botPlaces : Value → Place → List Place
  | .bot, q => [q]
  | .gloan _ w, q => botPlaces w q
  | .succ w, q => botPlaces w (.proj 0 q)
  | .borrow _ w, q => botPlaces w (.deref q)
  | .ind t c _ _ fs, q => botPlacesFields t c q 0 fs
  | _, _ => []
termination_by structural v => v

def botPlacesFields (t : String) (c : Nat) (q : Place) (i : Nat) : List Value → List Place
  | [] => []
  | w :: ws => botPlaces w (.field ⟨t, c, i, s!"f{i}"⟩ q) ++ botPlacesFields t c q (i + 1) ws
termination_by structural ws => ws
end

mutual
/-- Where `loan_l` sits inside a value, as steps from it. -/
def loanPath (v : Value) (l : Nat) : M (Option (List Step)) := do
  match v with
  | .loan m => pure (if m == l then some [] else none)
  | .gloan _ w => loanPath w l     -- static ends: a mark is not a step
  | .succ w => pure ((← loanPath w l).map (Step.proj 0 :: ·))
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

/-! ### Static ends: the places a returned borrow is lent

A call that returns a borrow lends it every place its borrow arguments lend, whether it runs or
closes off (rule 1), read from its declared type and its arguments, never from where the run
leaves the result pointing. A lent place keeps its content, marked `lent_ℓ v` (`Value.gloan`):
[Access] of the place, of a part of it or of a place containing it ends `ℓ` as a loan there
would (`firstLiveLoanOnPath`, `Value.loans`), paths go through the mark (`stepV`), and ending
`ℓ` removes the marks ([End ℓ]). So the generic call, where the call closes off and its fills
hold `ℓ`'s hole, and every instance, where it runs and the result points at one place, have the
same borrows live and the same places lent; and a fill re-run in a split world keeps its place
lent though its hole is gone. -/

/-- What `lendV` does to the marks of the borrow `l`. -/
inductive LendOp where
  /-- every place lent to `l` (its loan, or its mark) is lent to `g` too -/
  | mark (l g : Nat)
  /-- `l` has ended: each place it was lent becomes lent to the borrows in `l`'s final content
  (a reborrow of `*l` that outlives `l` keeps them lent), or free -/
  | ended (l : Nat) (to : List Nat)
  /-- D99: the borrow `l` is ended into the fresh borrow `g` that a call returns: every loan
  `loan_l` and mark `lent_l` becomes `g`'s, a renaming. A place that is then marked `lent_g`
  over a value already carrying `g`'s hole (marked by the call's rule 1 and by `l`) keeps one -/
  | into (l g : Nat)

/-- `w` is already a fill over the borrow `m` at its top: a sealed program over the hole `loan_m`
(a stuck call's fill, an unknown function of the hole), or marked `lent_m` (a known one). A bare
`loan_m` is not: the place a returned borrow points into is marked too, `lent_m loan_m` (the
identity), so that when `m` ends and a reborrow of `*m` outlives it, the whole place, not only the
reborrowed part, stays lent to the reborrow, as a sealed fill does at the generic call. -/
def carriesHole (m : Nat) : Value → Bool
  | .gloan l w => l == m || carriesHole m w
  | .sealed t => t.loans.contains m
  | _ => false

/-- Make `w` a fill over each of `to`: marked `lent_m w`, unless it already is one (a lent place
holds one fill per borrow it is lent to, in one of two forms: a sealed program over the hole, or a
known function of the hole, `lent_m v`, the identity `lent_m loan_m` included). -/
def lentTo (to : List Nat) (w : Value) : Value :=
  to.foldr (fun m acc => if carriesHole m acc then acc else .gloan m acc) w

/-- The live borrows a value is a fill over, at its top: its hole, a mark, or the holes inside a
sealed program (whose position inside it is unknown, so it is at the top, D29). -/
def fillHoles (env : Env) : Value → List Nat
  | .loan l => if liveLoan env l then [l] else []
  | .gloan l w => (if liveLoan env l then [l] else []) ++ fillHoles env w
  | v@(.sealed _) => liveLoansIn env v
  | _ => []

mutual
/-- Apply a `LendOp` to every mark and loan of a value, sealed programs and captures included
(a fill's hole sits inside its program). Marks do not change what a program computes, so a sealed
program is not re-run. -/
def lendV (fuel : Nat) (op : LendOp) (v : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some l := (match op with | .mark l _ | .ended l _ | .into l _ => some l) | return v
  if !(v.anyAtom fun | .loan m | .gloan m _ | .borrow m _ => m == l | _ => false) then return v
  match op, v with
  | .mark _ g, .loan _ => return .gloan g v
  | .into _ g, .loan _ => return .loan g
  | .into _ g, .gloan m w =>
    let w' ← lendV fuel' op w
    if m == l || m == g then return (if carriesHole g w' then w' else .gloan g w')
    return .gloan m w'
  | .into _ g, .borrow m w => return .borrow (if m == l then g else m) (← lendV fuel' op w)
  | .mark _ g, .gloan m w => if m == l then return .gloan g v else return .gloan m (← lendV fuel' op w)
  | .ended _ to, .gloan m w =>
    let w' ← lendV fuel' op w
    return (if m == l then lentTo to w' else .gloan m w')
  | _, .succ w => return .succ (← lendV fuel' op w)
  | _, .borrow m w => return .borrow m (← lendV fuel' op w)
  | _, .clo cs t rd => return .clo (← cs.mapM (lendV fuel' op)) (← lendT fuel' op t) rd
  | _, .tPi cs t rd => return .tPi (← cs.mapM (lendV fuel' op)) (← lendT fuel' op t) rd
  | _, .sealed t => return .sealed (← lendT fuel' op t)
  | _, .ind t c h ps fs => return .ind t c h ps (← fs.mapM (lendV fuel' op))
  | _, _ => return v
termination_by structural fuel

def lendT (fuel : Nat) (op : LendOp) (t : Term) : M Term := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let go := lendT fuel' op
  match t with
  | .val v => return .val (← lendV fuel' op v)
  | .assign p u => return .assign p (← go u)
  | .letIn h u w => return .letIn h (← go u) (← go w)
  | .seq u w => return .seq (← go u) (← go w)
  | .matchNat p z s => return .matchNat p (← go z) (← go s)
  | .fix h hs ds c d b => return .fix h hs ds c d (← go b)
  | .call f as hd => return .call (← go f) (← as.mapM go) hd
  | .succ u => return .succ (← go u)
  | .ascribe a b => return .ascribe (← go a) b
  | .prim n as => return .prim n (← as.mapM go)
  | .ctor ty c h ps as => return .ctor ty c h ps (← as.mapM go)
  | .matchInd p ty as => return .matchInd p ty (← as.mapM fun (h, a) => do pure (h, ← go a))
  | .block cs rd pf B m => return .block (← cs.mapM fun (h, a) => do pure (h, ← go a)) rd pf B (← go m)
  | _ => return t
termination_by structural fuel
end

/-- `lendV` at every value of Ω (types hold no loan: they are formed on a private copy). -/
def lendEnv (fuel : Nat) (op : LendOp) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  mapState (lendV fuel' op) false
termination_by structural fuel

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
    | .gloan _ w => ctorFieldsF fuel' w g
    | .loan l =>
      let env := (← get).env
      match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
      | some (c, _) => ctorFieldsF fuel' c g
      | none => pure none
    | _ => pure none
  termination_by structural fuel

/-- D64 [Open]: `p` is a data field whose declared type mentions earlier fields (its
assignment is a strong update), and (D112) a tree field: its declared type is a data inductive
at every instance. -/
def strongUpdate (p : Place) : M Bool := do
  let .field g _ := p | return false
  let some d := (← get).inds.find? (·.name == g.ty) | return false
  -- D112: a leaf field is never strongly updated (`Decide.fieldIsLeaf`)
  pure (d.fieldDependent g.ctor g.idx && !(← fieldIsProof g) && !(← fieldIsLeaf (← fuelLeft) d g.ctor g.idx))

/-- D64: does a value hold a value of a dependent constructor (outside sealed programs and
closures, which carry their types)? -/
def hasDependent (v : Value) : M Bool := do
  match v with
  | .ind t c _ _ fs =>
    if (← lookupInd t).dependent c then return true
    anyList fs
  | .borrow _ w | .succ w | .gloan _ w => hasDependent w
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
copy of the state, by the ordinary rules. An argument of borrow type cannot: the borrow must be
the real one (a copy's borrow would alias the place it borrows), so it runs in place. Which, is
decided by the argument's declared type (`Decide.stmtArgInPlace`). -/
def stmtArgIf (fuel : Nat) (b : Bool) (a : Term) (x : M (Value × Option Value)) : M (Value × Option Value) := do
  if !b then return ← x
  if ← stmtArgInPlace fuel a then x else inStatement x

def fixOf (fv : Value) : M (List Value × Term × List (DeclInfo × Value)) := do
  match fv with
  | .gfn n => match (← lookupGlobal n).fn? with
    | some t => pure ([], t, [])
    | none => err s!"{n} is not a function"
  | .clo cs t rd => pure (cs, t, rd)
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

/-- D78 [Rec]: for each variable a closure formed from `t` captures, in `capture`'s order
(oldest binding first), the mark of the binding it captures: whether it is some function's
binding of itself, or a capture of one. Read from the bindings themselves, never from their
values: capturing a function value that is not a copy moves it, leaving `⊥` behind, but the
binding keeps its mark. -/
def capMarks (t : Term) : M (Array (Option Nat)) := do
  let fvs := (t.freeVars.toArray.qsort (· > ·)).toList
  let top := (← get).env.back!
  pure (fvs.toArray.map fun o => (top.binds[top.binds.size - 1 - o]?).bind (·.recUid))

/-- D78: mark the top frame's capture bindings (the first `marks.size` bindings) with the
marks `capMarks` read. -/
def markCapRec (marks : Array (Option Nat)) : M Unit := do
  let f ← topIdx
  modifyFrame f fun fr => Id.run do
    let mut bs := fr.binds
    for (m, i) in marks.toList.zipIdx do
      if let some u := m then
        if i < bs.size then bs := bs.modify i ({ · with recUid := some u })
    pure { fr with binds := bs }

/-- D78: mark the top frame's last binding as the binding of itself of the function whose
mark is `uid` (every function's check takes a fresh one; it is its [Rec] frame's when it declares
`by`, D136's amendment). -/
def markLastRec (uid : Nat) : M Unit := do
  let f ← topIdx
  modifyFrame f fun fr =>
    if fr.binds.size == 0 then fr
    else { fr with binds := fr.binds.modify (fr.binds.size - 1) ({ · with recUid := some uid }) }

/-- D78 [Rec]: the frame mark of a call's head, when the head is a variable: the
`Binding.recUid` of the binding it names (a function's binding of itself, or a closure's
capture of it), else `none`. -/
def callRecUid (f : Term) : M (Option Nat) := do
  match f with
  | .place (.var x) =>
    match ← varPos x with
    | .bind fr i => pure ((← get).env[fr]!.binds[i]!.recUid)
    | .temp _ _ => pure none
  | _ => pure none

/-- D78 [Rec]: is a call of `fv`, made through a binding marked `uid?`, a recursive call of
the function `ctx` is checking? The one place that decides it. It is read from syntax: the
call's head is the name the function binds for itself, or a closure's capture of that name
(`Binding.recUid`). Comparing function values cannot decide it: a refinement, an [End] or a
re-normalisation substitutes inside a local function's captured values (its own binding of
itself included) but not inside the frame, so after `match n {…}` on a captured `n` the
refined closure no longer equals the one being checked and its recursive calls went
unchecked (rec-model's `CapSplit`, a closed proof of `False`). Value equality is kept only
as a fail-safe that can add a check, never remove one. Since D136 a local function is not
recursive and every frame is a top-level definition's, whose value is its name, so the mark and
the value agree at every call that is made (measured over the suite at D136's landing: no call
had the mark without the value). -/
def recFrameOf (ctx : RecCtx) (fv : Value) (uid? : Option Nat) : Bool :=
  uid? == some ctx.uid || ctx.fn == fv

/-- D135: is `fv` a function whose check is under way (its frame on the [Rec] stack)? Its body is
code the check has not finished with, so it is never run: a call of it closes off at once, as a
call of an unknown function does (`callFn`, the one place a body is run), and its body runs only
once its definition is accepted, as in Lean, where the function being defined does not unfold
inside its own body. Since D136 the stack holds top-level definitions only, so this compares
names: a global function value is its name, which no refinement or [End] changes, whichever route
reaches the call (by its name; a sealed program's head call, re-run after a split; a λ's capture
of it, run untyped; a sealed program's typing, `sealedType?`). (D135 compared code, a closure's
`fix` term without its embedded values, for local recursive functions, whose values a refinement
changes; a local function being checked cannot be called during its check, D136.) -/
def underCheck (fv : Value) : M Bool := do
  pure ((← get).recStack.any (·.fn == fv))

/-- [Rec]: at a recursive call, a parameter position survives if its argument (the
content, through a borrow) is a strict subterm of that parameter's entry value as
refined so far. The recursive position is any position that survives every call.
Every enclosing function being checked is considered, so a recursive call inside a
nested closure is checked against the outer function's entry values (fix L3). -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 15): the entry value as refined so far; refinement only adds constructors, so a strict subterm found here is one at every instance.
def recCheck (fv : Value) (ws : Array Value) (uid? : Option Nat := none) : M Unit := do
  let st ← get
  let mut frames := #[]
  for ctx in st.recStack do
    if ctx.tests && recFrameOf ctx fv uid? then
      let cands := ctx.cands
      let cands' ← cands.filterM fun j => do
        match ctx.entries[j]?.join, ws[j]? with
        | some σ, some w =>
          let u := match w with | .borrow _ u => u | u => u
          return (strictSubterms (← expandRefs st.refs (.abs σ))).contains u
        | _, _ => pure false
      -- a call that fails the test rejects the definition here, at the call; the call itself is
      -- never run, whatever the test says (D135: a function being checked closes off)
      if cands'.isEmpty then
        err s!"[Rec] at {fv}({", ".intercalate (ws.toList.map toString)}): the argument in the decreasing position is not a strict subterm of that parameter's entry value as refined so far"
      frames := frames.push { ctx with cands := cands' }
    else frames := frames.push ctx
  set { st with recStack := frames.toList }

/-- D108: the σ a [Split] generalised the sealed program `v` to, if any. The record is a key,
so it is compared exactly (`Value.exact`: recorded parameters and binder names included), not up
to conversion's `==`, under which `Nil` recorded at `List(Nat)` and at `List(Unit)` are equal. -/
def neutralLookup (v : Value) : M (Option Nat) := do
  pure (((← get).neutrals.find? (·.1.exact v)).map (·.2))

/-- D84: the value a sealed program stands for in this world, when a [Split] here generalised it
(on any private copy: records survive copies, D37), as `canonNeutral` gives it. -/
def recordedNeutral (v : Value) : M (Option Value) := do
  match v with
  | .sealed _ => match ← neutralLookup v with
    | some σ => pure (some (← expandRefs (← get).refs (.abs σ)))
    | none => pure none
  | _ => pure none

/-- Finding G1: a neutral that a [Split] generalised stays generalised when normalisation
derives it again (it is a closed, deterministic computation, so every derivation of it
denotes the same value). Returns its refined value if it is one. -/
def canonNeutral (v : Value) : M Value := do
  match v with
  | .sealed _ => match ← neutralLookup v with
    | some σ => expandRefs (← get).refs (.abs σ)
    | none => pure v
  | _ => pure v

/-- Two steps name the same part: `.i` of a value of a type with one constructor is that
constructor's field `i` (D81: the surface writes both, `p.i` and a pattern variable; a Nat's
`.0`, its predecessor, is never a constructor field). -/
def stepEq : Step → Step → Bool
  | .proj i, .field g | .field g, .proj i => g.ctor == 0 && g.idx == i
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
  | .clo cs _ _ | .tPi cs _ _ => valsIn cs
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
    -- exp-block-text: a sealed block's values are its cells'
    | .block cs _ _ _ _ => armsIn cs
    | _ => []
  termination_by structural t => t
  termsIn : List Term → List Term
    | [] => []
    | t :: ts => termVals t ++ termsIn ts
  termination_by structural ts => ts
  armsIn : List (Hint × Term) → List Term
    | [] => []
    | (_, t) :: ts => termVals t ++ armsIn ts
  termination_by structural ts => ts

/-- One arm of a stuck block (`closeBlock`): `setup` puts the state in the arm's world and
returns what it did (a [Split] arm refines the scrutinee and returns the refinement; the
transported term of a closed-off `J` has nothing to set up), and `body`, given that, checks the
arm and returns its result and type. The block runs both itself, so that no block can be formed
without its arms having been checked to their return (the producer obligation, D76). -/
structure BlockArm where
  setup : M Value
  body : Value → M (Value × Value)

/-- D89: the variables a field type determines when matched against a value's type: the
type itself, and the arguments of an inductive type former, not what a type function or a
Π-type does with its arguments. -/
def Term.rigidVars : Term → List Nat
  | .place (.var j) => [j]
  | .tind _ as => (as.attach.map fun ⟨a, _⟩ => a.rigidVars).flatten
  | .ref A => A.rigidVars
  | _ => []

/-- D89: an untyped run cannot infer the parameters of `d`'s constructor `c` from its fields
(D88's inference) when some parameter is determined by no field whose type is not a
proposition (`Term.rigidVars`): it has no fields, a phantom parameter, only proof fields
(`Dec`'s `Yes(h : P)`, which untyped runs do not evaluate), or only fields whose types a type
function computes from it (`DP`'s `y : G(n, x)`). D105: a field determines a parameter only
where it is inferred from it (`Decide.inferFrom`), as typing infers it. In every field's type the
parameters are `var 0 … var (np - 1)`, the last `var 0`, whatever the field's position (the
fields come after them, `IndDecl.fieldRefs`); before D105 this read field `i`'s parameter `k` as
`var (i + np - 1 - k)`, right only for the first field, and `MkR(x : A, y : A)` read as
determining `R`'s phantom `B`, so an untyped run built it recording no parameters. -/
def ctorNeedsCtx (fuel : Nat) (d : IndDecl) (c : Nat) : M Bool := do
  let np := d.params.length
  match d.ctors[c]? with
  | none => pure false
  | some (_, fields) =>
    let isProp (FT : Term) : Bool := match FT with
      | .eq .. | .id .. => true
      | .place (.var j) => j < np && (match d.params[np - 1 - j]? with
          | some (_, .sort 0) => true
          | _ => false)
      | _ => false
    let rigid ← fields.mapM fun (_, FT) => do pure (← inferFrom fuel FT).rigidVars
    pure <| (List.range np).any fun k =>
      !(fields.zipIdx.any fun ((_, FT), i) => !isProp FT && (rigid.getD i []).contains (np - 1 - k))

/-- D89: does a tail of `t` (through `let`, `;` and match arms) build a constructor whose
parameters are not written and that its fields do not determine (`ctorNeedsCtx`), or one of
whose fields is such a constructor (`Some(None)`)? Read from
syntax and declarations; an untyped run then gave `t` the type its context declares. D124: no
longer read by the machine, which hands a hint exactly where typing does (`readsHint`); kept, with
`ctorNeedsCtx`, because the proof line's files name them. -/
def needsCtx (fuel : Nat) (t : Term) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match t with
  | .ctor ty c _ [] as =>
    -- or a field needs it, which then takes its type from this constructor's parameters
    if ← ctorNeedsCtx fuel' (← lookupInd ty) c then return true
    as.anyM fun a => needsCtx fuel' a
  | .letIn _ _ w | .seq _ w => needsCtx fuel' w
  | .matchNat _ z s => pure ((← needsCtx fuel' z) || (← needsCtx fuel' s))
  | .matchInd _ _ arms => arms.anyM fun (_, a) => needsCtx fuel' a
  | _ => pure false

/-- D124: does the run of `t` read the hint it is handed? `evalCore` reads it at a constructor whose
parameters are not written, of an inductive that has some (the hint gives them, before the fields);
at an embedded value, `rewrite` and `rewriteR` as their type (the untyped run returns the hint as
their type), which is read only where the context reads the term's type (`typeRead`: a borrow
argument, whose type is its cell's at [Close]; nowhere else the untyped run hands a hint); through
`clone`, `peek` and `inplace` (which hand it to their operand); and, in tail position (`tail`),
through a `let`'s or a `;`'s tail, a match's arms and a split's term (D125). Nothing else reads it (a hole is stuck in an
untyped run). Read from syntax and declarations. The untyped run hands a hint exactly where the
typed check does; where the term would not read it, it is not computed, which no run can tell from
computing it. -/
def readsHint (fuel : Nat) (tail typeRead : Bool) (t : Term) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match t with
  | .ctor ty _ _ ps _ => pure (ps.isEmpty && !(← lookupInd ty).params.isEmpty)
  | .val _ | .prim "rewrite" _ | .prim "rewriteR" _ => pure typeRead
  | .prim "clone" [u] | .prim "peek" [u] | .prim "inplace" [u] => readsHint fuel' false typeRead u
  | .letIn _ _ w | .seq _ w | .prim "split" [_, w] => if tail then readsHint fuel' true typeRead w else pure false
  | .matchNat _ z s =>
    if tail then pure ((← readsHint fuel' true typeRead z) || (← readsHint fuel' true typeRead s)) else pure false
  | .matchInd _ _ arms => if tail then arms.anyM fun (_, a) => readsHint fuel' true typeRead a else pure false
  | _ => pure false
termination_by structural fuel

/-- D124: the declared codomain of `piTy` at `ws`, not yet evaluated: a hint `forceHint` evaluates
where it is read. A sealed program whose head is no call, so nothing but `forceHint` reads it. -/
def hintLater (piTy : Value) (ws : Array Value) : Value :=
  .sealed (.prim "⋄hint" (.val piTy :: ws.toList.map Term.val))

/-- D117: what a field's value stands for in the frame that types a later field (`fieldTypesOf`):
each live loan resolved to its borrow's content, recursively, and each mark to the content it marks,
as `valType?` reads a loan and a mark for typing. So that frame binds no second occurrence of a
loan, and a later field's type is computed at the index's current content; a read of the index
there ends no borrow. A loan whose borrow is not in Ω stays as it is. -/
def resolveLoans (fuel : Nat) (v : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match v with
  | .loan l =>
    let env := (← get).env
    match (findBorrow env l).bind fun p => (valAt env p).takeBorrow l with
    | some (c, _) => resolveLoans fuel' c
    | none => pure v
  | .gloan _ w => resolveLoans fuel' w
  | .succ w => pure (.succ (← resolveLoans fuel' w))
  | .ind t c h ps fs => pure (.ind t c h ps (← fs.mapM (resolveLoans fuel')))
  | _ => pure v
termination_by structural fuel

/-- D131 (a safety net of the typed check): a binding a typed run makes (a `let`, a parameter of
the function being checked, a λ's parameter) agrees with its stored type and with the value bound.
The class its declared reading `d` gives it (a proof; a type; data) is the class of its stored type
`T` (a proposition; a sort; anything else), and a proof value `⋆` is read as a proof. The readers
see a sort only where one is written (D55): through a call of a function whose body is a sort
(`PropF(x)` with `PropF (n : Nat) : Type₁ := Prop`), a constant or an ascription, a type reads as
data, and so does a proof whose type is formed from it (`J` through a motive
`λ(x : Nat) : PropF(x) => ⊤`). Decisions that consume the reading then disagree with the run (the
join moved a proof read as data at an instance: D131's `V1`). The value is compared as well as the
type because a stored type can be stuck on a hidden sort (an unknown's or a sealed type, classed as
data) while the value is already `⋆`. The other way, a binding read as a proof holds `⋆` or a
stand-in whose content is not known yet (an unknown `σ`, at a proposition the run cannot evaluate;
a sealed program); any other value read as a proof is rejected too. An unknown reading (a hole's)
is not tested. -/
def readingAgrees (fuel : Nat) (h : Hint) (T : Value) (d : DeclInfo) (v : Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if d matches .any | .conflict then return
  let cls (k : Nat) : String := match k with | 0 => "a proof" | 2 => "a type" | _ => "data"
  let hidden := "a sort is hidden from the reading, behind a call of a function whose body is a sort, a constant, an ascription or a match whose arms disagree; write the sort itself there"
  let rd : Nat := if d.isProof then 0 else if d matches .sort _ then 2 else 1
  let ty : Nat ← if T matches .sort _ then pure 2 else if ← isPropV fuel' T then pure 0 else pure 1
  unless rd == ty do
    let what := match ty with
      | 0 => s!"its type {T} is a proposition"
      | 2 => s!"its type {T} is a sort"
      | _ => s!"its type {T} is neither a sort nor a proposition"
    err s!"[D131] {h.name} is {cls ty} ({what}), but its declared type reads as {cls rd}: {hidden}"
  if v == .proof && rd != 0 then
    err s!"[D131] {h.name} holds a proof (⋆, its type {T}), but its declared type reads as {cls rd}: {hidden}"
  if rd == 0 && !(v matches .proof | .abs _ | .sealed _) then
    err s!"[D131] {h.name} is read as a proof, but holds {v}, which is not a proof (its type {T})"

/-- D134: a call's head type, as the untyped run has it (`funType`: the caller's stored type for the
head, else the value's own), is a function type written as one, of the call's arity. `declCallType`
tests it before it computes the call's type, and `callFn`'s deferred path (a `let` bound to the call,
`later`) tests it when it records the type for later: deferral postpones computing a type, not the
test that there is one. One function, so the two paths cannot drift. -/
def callPi (piTy : Value) (n : Nat) :
    M (List Value × List Hint × List Term × Term × List (DeclInfo × Value)) := do
  let .tPi cs (.pi hs ds c) rd := piTy | err s!"not a function type: {piTy}"
  if ds.length != n then err s!"arity: {ds.length} parameters, {n} arguments"
  pure (cs, hs, ds, c, rd)

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
  -- D108: the target is found exactly (`Value.exact`), as a key: at a sealed program, its recorded
  -- parameters and binder names count; at `σ` or a loan it is the same as `==`
  if !(v.anyAtom (·.exact x)) then return v
  if v.exact x then return r
  match v with
  | .abs _ | .loan _ => return (if v.exact x then r else v)
  | .succ w => return .succ (← substV fuel' x r w)
  | .borrow l w => return .borrow l (← substV fuel' x r w)
  | .gloan l w => return .gloan l (← substV fuel' x r w)
  | .clo cs t rd =>
    let rd' ← rd.mapM fun (d, T) => do pure (d, ← substV fuel' x r T)
    return .clo (← cs.mapM (substV fuel' x r)) (← substT fuel' x r t) rd'
  | .tPi cs t rd =>
    let rd' ← rd.mapM fun (d, T) => do pure (d, ← substV fuel' x r T)
    return .tPi (← cs.mapM (substV fuel' x r)) (← substT fuel' x r t) rd'
  | .sealed t => nfSealed fuel' (← substT fuel' x r t)
  | .tEq A a b => mkEqM fuel' (← substV fuel' x r A) (← substV fuel' x r a) (← substV fuel' x r b)
  | .tInd n as => return .tInd n (← as.mapM (substV fuel' x r))
  | .tRef A => return .tRef (← substV fuel' x r A)
  | .ind t c h ps fs => return .ind t c h (← ps.mapM (substV fuel' x r)) (← fs.mapM (substV fuel' x r))
  | _ => return v
termination_by structural fuel

def substT (fuel : Nat) (x r : Value) (t : Term) : M Term := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if !(t.anyAtom (·.exact x)) then return t
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
  | .ref u => return .ref (← go u)
  | .cong a b => return .cong (← go a) (← go b)
  | .ascribe a b => return .ascribe (← go a) (← go b)
  | .eq a b c => return .eq (← go a) (← go b) (← go c)
  | .id a b c => return .id (← go a) (← go b) (← go c)
  | .prim n as => return .prim n (← as.mapM go)
  | .ctor ty c h ps as => return .ctor ty c h (← ps.mapM go) (← as.mapM go)
  | .tind n as => return .tind n (← as.mapM go)
  | .matchInd p ty as => return .matchInd p ty (← as.mapM fun (h, a) => do pure (h, ← go a))
  -- exp-block-text: a sealed block's cells, their declared types, its type and its match
  | .block cs rd pf B m =>
    let rd' ← rd.mapM fun (d, T) => do pure (d, ← substV fuel' x r T)
    return .block (← cs.mapM fun (h, a) => do pure (h, ← go a)) rd' pf (← substV fuel' x r B) (← go m)
  | _ => return t
termination_by structural fuel

/-- Substitute in every value of Ω; with `types`, also in the stored types, the types
of abstract values and the goal ([Split]: "applied to Ω, the goal and all stored
types"). Without `types` (the fill of a loan, [End]): types hold no live loan, since a type
is formed on a private copy, where reading a place ends every loan inside it. The
positions are `mapState`'s, the same `renormAll` reaches. -/
def substEnv (fuel : Nat) (x r : Value) (types : Bool) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- a type's sealed programs re-run as types: erased, reads copy (D53, fuzz-port RN)
  mapState (fun v => substV fuel' x r v) types
termination_by structural fuel

/-- [Seal] `nf(⌈t⌉)`: run `t` from the empty environment. Its head call is marked
(`Term.call _ _ true`) and is not eligible for [Close]; loans whose borrow is outside
the run are inert (they have no borrow in the run's Ω). If the run completes, the
result is its value; if it is stuck, `⌈t⌉` (its embedded values are already normal).

The only place a sealed program is re-run (`substV` after a substitution into it, `renormV`
after a generalised neutral is refined, both at every position `mapState` reaches): closing
off's (C4), a sealed program runs again exactly when something it depends on changes, wherever
it occurs (`notes/closeoff-model.md`).

D97: a sealed program whose text holds a loan is never run. Such a loan is a hole by
construction, whether or not its borrow is in Ω yet (a fill, the value a stuck call or block
left at a place it lends to a borrow still live; `closeCall`'s `&T` row substitutes a fill
over `loan_k` before `borrow_k` is in Ω). The program is left as it is: a substitution into it
is made on its text, and its marks and their transfer at [End] are unchanged. It sits at a
lent place, which no access reaches without ending that borrow first (D90), and ending the
last of its borrows substitutes the borrow's final content for the last hole (`endBorrow`,
`substV`), which is the run that computes it. -/
def nfSealed (fuel : Nat) (t : Term) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D97: a sealed program whose text holds a loan (a hole: a fill, or a program a substitution
  -- has just put a hole into) is left as it is, never run: what its run would compute cannot be
  -- observed while its borrows live, and ending the last of them runs it
  if t.hasLoanAtom then
    fire .SealHole fun _ => s!"left sealed: its text holds a hole ({(Value.sealed t).loans.eraseDups})"
    return .sealed t
  let saved ← get
  -- bounded like calls, so that a normalisation loop (breaker-fresh-v16 X5 without D39)
  -- is an error rather than a stack overflow
  if saved.depth ≥ 2000 then exhausted "normalisation depth exceeded (a sealed program that re-closes itself)"
  modify fun s => { s with env := #[{}], obsFrame := none, depth := s.depth + 1 }
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
    -- D84 [Id-typestate], ending a borrow: a side of `Id` may not end a borrow that a binding
    -- or a temporary outside it holds ([Access] of what it borrows, [Drop] of what it points
    -- to): a continuation could use the borrow after the other side and not after this one.
    -- Assigning over the binding re-points it (`assignPlace`), which the type-state compares.
    -- D114: a binding the side consumes (`own`, its type-state's, from syntax) is exempt: the side
    -- moves it on every path, so no continuation uses it after either side, and where its borrow
    -- ends is the path's (a call's or a stuck block's parameter dies, or the join drops it here)
    -- Two paths, value-dependent by design (notes/two-paths-census.md, site 28): the frame's loans at formation are the run's; the check only rejects, a borrow the checked run has already ended is one the program cannot use after the `Id`, and a side's access at an instance is an access on the checked run (a stuck block takes every place any arm uses); D114: a consumed binding is exempt, read from syntax, so where its borrow ends (by path) is never asked.
    if let some (f0, n0, t0, own) := (← get).obsFrame then
      match p with
      | .bind f i =>
        if f == f0 && i < n0 && !own.contains i then
          let y := env[f]!.binds[i]!.hint.name
          fire .IdTypestate fun _ => s!"a side ends the borrow {y}"
          err s!"[Id-typestate] a side of Id ends the borrow {y}, which a binding outside the Id holds (the side uses or drops what {y} borrows): end it before the Id"
      | .temp f i =>
        -- a borrow in flight around the `Id`: an argument evaluated before it, a scrutinee
        if f == f0 && i < t0 then
          fire .IdTypestate fun _ => s!"a side ends a borrow in flight"
          err s!"[Id-typestate] a side of Id ends a borrow that a value in flight around the Id holds (an argument evaluated before it): form the Id outside that expression"
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
      -- D98: in an observation's ends as anywhere: a side of `Id` that leaves a borrow's content
      -- moved out is rejected when the observation ends it, as the same code is when it is run
      if c.hasHole then
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
      -- static ends: the places lent to `l` stay lent to the borrows its final content holds (a
      -- reborrow of `*l` that outlives it), as a stuck call's fills then hold their loans; else free
      lendEnv fuel' (.ended l (liveLoansIn (← get).env c))
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
      | some T => pure (.abs (← freshAbsR fuel' T))
      | none => pure v
    | none => pure v
  -- static ends: a mark says which borrow may point here, not that its content is gone; the
  -- loans inside it say what is lent out (a stuck call's fill there is read whole, as before)
  | .gloan _ w => lentUnknown fuel' w
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
sealed program is a call ([Close]) of a function value, or a stuck block's text; every function
value a checked program can call is either its caller's abstract value, or formed by a check that
ends here: [Def] and [Fix] (`checkFix`) at their body's return, whose borrow parameters are real
borrows that the frame's pop then ends ([End], which repacks them too); and a stuck block's text
(`closeBlock`, exp-block-text) is checked here at the end of each arm, where the cells it reaches
through a borrow are the places it takes by `&`, given here as `lent`. -/
def bodyReturns (fuel : Nat) (what : String) (v T : Value) (lent : List Place) (lentWhat : String) :
    M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  fire .Return fun _ => s!"{what}: {v} : {T}, with {lent.length} place(s) held by borrow"
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

/-- [Obs] and [Obs-borrow] (notes/id-model.md): the one place a computation's result is
observed. With the result `r` held as a temporary, end every remaining borrow, and return the
result as it is then. A borrow-typed result `borrow_k u` given a fresh `σw` is observed by
[Obs-borrow]: `σw` is written through the borrow first (`*r := σw`), so the owners of `loan_k`
show where it pointed, and the observed result is `u`'s final content. `Id`'s sides
(`observe`) and [Conv-fun]'s generic calls (`convFnRun`) both observe through here, alike: a
borrow ending over a moved-out part is an error here as anywhere ([End], D53; D98 removed D68's
exception for `Id`, under which such a part was read as `⊥`). `T` is `r`'s type, as its caller
has it (D104: the temporaries' stored types; a borrow's content is held at the content of its
type `&C`). -/
def obsResult (fuel : Nat) (r : Value) (T : Option Value) (σw? : Option Nat) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match r, σw? with
  | .borrow k u, some σw =>
    pushTemp u (match T with | some (.tRef C) => some C | _ => none) "obsResult"
    pushTemp (.borrow k (.abs σw)) T "obsResult"
    endAll fuel'
    discard popTemp
    popTemp
  | _, _ =>
    pushTemp r T "obsResult"
    endAll fuel'
    popTemp
termination_by structural fuel

/-- [Frame] F4 (`notes/frame-model.md`): in a run whose effects persist, a loan in the top frame
is borrowed from the top frame.
Nothing below the running code can hold a borrow of a place it owns: there are no borrows in data
and no borrows of borrows, a closure captures no borrow, and a borrow of a local never outlives it
([Drop]). So [Access] and [Drop], which start from a place of the top frame, only ever end a
borrower of the top frame, and the frame property's one channel downward stays the borrows the
frame holds (their [End] writes the lender's place). This is the single place they end such a
borrow, and it asserts F4 rather than trusting it: a violation is an internal error, never a
silent write below the frame. Inside a private copy (`privateDepth > 0`) F4 need not hold: the
checker's scaffolding binds copies of stored values in frames of its own, and a copy may hold a
live loan whose borrower is below; whatever [Access] ends there is discarded with the copy. D117
removed the commonest such copy (the frame that types a dependent field binds what a lent field
stands for, `resolveLoans`, so `DepFields.CellGet` no longer copies a loan), but not all: with F4
made strict inside private copies too, rejected rows of `OpenAttacks` and `DepVec` are rejected by
this internal error instead of their reasons (checked 2026-11-22). -/
def endTopLoan (fuel : Nat) (l : Nat) (site : String := "") (p? : Option Place := none) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let env := (← get).env
  match findBorrow env l with
  | some (.bind f _) | some (.temp f _) =>
    if f + 1 != env.size && (← get).privateDepth == 0 then
      err s!"internal: [Frame] {site}: the loan {l} lies in the top frame but is borrowed from frame {f} below it (F4)"
  | none => pure ()
  -- D106: no access ends a borrow a value in flight holds (a temporary: a call's earlier argument,
  -- an arm's result across the join, a result across a `let`'s drop or a frame's pop). The one
  -- place every [Access] ends a borrow, so the rule is stated once. Outside private copies: a
  -- statement's run on its copy reads the current content and ends a borrow on the copy only,
  -- which is discarded (`SubM(&*x, 0, LeZero(*x))` is accepted)
  if let some (.temp _ _) := findBorrow env l then
    if (← get).privateDepth == 0 then
      let what ← match p? with
        | some p => pure s!"reading or writing {← ppPlace p}"
        | none => pure "an access"
      err s!"[Access] {what} ends a borrow that a value in flight holds (an earlier argument of a call, or a result on its way out): it would hold a borrow that has ended (D106)"
  endBorrow fuel' l
termination_by structural fuel

/-- [Access], path part: end every borrow whose loan is on the path to `p`. -/
def accessPath (fuel : Nat) (p : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (i, ss) := p.steps
  let env := (← get).env
  match firstLiveLoanOnPath env (valAt env (← varPos i)) ss with
  | some l => endTopLoan fuel' l "accessPath" (some p); accessPath fuel' p
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
  | l :: _ => endTopLoan fuel' l "accessInside" (some p); accessInside fuel' p owned
  | [] => pure ()
termination_by structural fuel

/-- D64 [Open], D112: a write or borrow through an index field of a dependent constructor value
invalidates the fields whose types mention that field and that cannot be typed by what they
hold: the proof fields (a proof is `⋆` and carries no type, so a stale one could not be told
apart at the repack) and the LEAF fields (D112, `Decide.fieldIsLeaf`: a number, the unit value or
a function does not say which instance of the field's type it was written at, and the set model
reads a leaf at its field's declared type). They become `⊥` until assigned again; an assignment
is checked against the telescope at the current contents. A leaf that is lent is accessed first
([Access]: its borrows end), as a write to it would be. -/
def openWrite (fuel : Nat) (p : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for (q, g) in p.fieldPrefixes do
    let some d := (← get).inds.find? (·.name == g.ty) | continue
    unless (d.indexFields g.ctor).contains g.idx do continue
    for ((fname, FT), j) in ((d.ctors[g.ctor]!).2).zipIdx do
      if j != g.idx && (d.fieldRefs g.ctor FT).contains g.idx then
        let proof ← fieldTermIsProp d FT
        let leaf ← if proof then pure false else fieldIsLeaf fuel' d g.ctor j
        if proof || leaf then
          let fp := Place.field ⟨g.ty, g.ctor, j, fname⟩ q
          if (← content? fp).isSome then
            if leaf then accessInside fuel' fp
            fire .Open fun _ => s!"a write through {g.name} invalidates the {if proof then "proof" else "leaf"} field {fname}"
            setPlace fp .bot
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
    | l :: _ => endTopLoan fuel' l "neutralHead" (some p); accessNeutralHead fuel' p
    | [] => pure ()
  | _ => pure ()
termination_by structural fuel

/-- [Read]: reading a place moves its content out (`p ↦ ⊥`), in any term: a statement runs on
its own private copy, so its moves are undone with the copy (one mental model, D68). Content
is copied ([Copy]) when the place's declared type is a copy type (`copyRead`, D80), and by
`clone`. A place partly moved out cannot be read (D53 (h)). -/
def readPlace (fuel : Nat) (p : Place) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  accessPath fuel' p; accessInside fuel' p
  let v ← content p
  -- D111: every loan outside a sealed program is live; after the access ended the live ones
  -- inside, none is left (a loan whose borrow is gone would be read as data of any type)
  if v.outerLoans.any (!liveLoan (← get).env ·) then
    err s!"INTERNAL [Read] {← ppPlace p} holds a loan whose borrow is not in Ω (D111: every loan outside a sealed program is live; please report)"
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
  | .borrow _ c =>
    -- D127: a borrow is read whole as any value is (D53): one whose content is partly moved out is
    -- not a member of `&T` (the model reads only whole members), and could reach code that
    -- assumes its content whole; restore the content through it first. In every mode of the read
    -- (moving, copying, in place: this branch is taken in each)
    if c == .bot then
      err s!"[Read] {← ppPlace p} is a borrow whose content was moved out: refill it through {← ppPlace p} (*{← ppPlace p} := …) before reading {← ppPlace p} (D127)"
    if c.hasHole then
      err s!"[Read] {← ppPlace p} is a borrow whose content is partly moved out ({c}): restore it before reading {← ppPlace p} (D127)"
    logEffect p "moves"; setPlace p .bot; pure v
  | _ =>
    if v == .proof then return v
    -- D127: a partly moved place is not read by copy either (`clone`, `peek`, an erased read). A
    -- place of a copy type is never moved, so never partly moved: the `⊥` it can hold is inside a
    -- stuck proposition (D68, below), and it is read whole
    if (← get).copying then
      if v.hasHole && !(← copyRead fuel' p) then
        err s!"[Read] {← ppPlace p} was partly moved out, and is not copied either (D127)"
      return v
    -- read in place: not consumed, but it must be there (D53: a call's head, the Fn rule;
    -- a stuck block's read-only capture, as the match inspects its place)
    if inPlace then
      if v.hasHole then err s!"[Read] {← ppPlace p} was partly moved out (D53)"
      return v
    -- a copy-type value is read whole whatever it holds (a proposition whose stuck equation
    -- mentions a moved place, D68)
    if ← copyRead fuel' p then
      fire .Copy fun _ => "its declared type is a copy type (D80)"
      return v
    if v.hasHole then err s!"[Read] {← ppPlace p} was partly moved out (D53)"
    if !erased && (← isCapture p) then
      err s!"[D53] a closure's body moves a captured value out ({← ppPlace p}); a closure may run again: clone it"
    fire .Read fun _ => "its declared type is not a copy type: moved out"
    logEffect p "moves"
    setPlace p .bot
    pure v
termination_by structural fuel

/-- D53, D80 [Read]: reading `p` copies exactly when its declared type reads as a copy type
(`Decide.declCopy`), read by the one reader of declared types: a variable's binding's reading
(a parameter's written type, a `let`'s annotation or right-hand side, a capture's binding's),
a field's at its parent's (`Decide.placeDecl`). Never its stored (evaluated) type or its
content's constructor, so the generic call and every instance decide it alike: a parameter
`x : A` moves at an instance `A := Word` as at the generic call (a generic `T` in Rust is never
`Copy`), and a Π-typed place moves whatever function it holds (D68). -/
def copyRead (fuel : Nat) (p : Place) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  declCopy fuel' (← withLive true (placeDecl fuel' [] p))
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

/-- [Assign] with the value already computed: drop the old content, store the new. D115: the value
is the top temporary of the current frame, pushed by the caller with its type (D104) as soon as
it was computed, and held there while the caller checks it and while the old content is
dropped. -/
def assignPlace (fuel : Nat) (p : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D67: a loan behind a borrow the old content holds is not ended: [Drop] of the old borrow
  -- ([End]) carries it back to its owner, where it stays live (reborrow-and-replace,
  -- `x := &(*x).f`). Loans in the owned part, neutrals there included, still end
  accessPath fuel' p; accessInside fuel' p true
  let old ← content p
  unsizedCheck p old "assigned"
  -- D111: a borrow is a whole position's value (D48), so none lies below the old content's root,
  -- where overwriting it would end nothing and leave its lender a loan forever
  if old.borrowBelowRoot then
    err s!"INTERNAL [Drop] the old content of {← ppPlace p} holds a borrow below its root (D111: a borrow is a whole position's value; please report)"
  match old with
  | .borrow l _ =>
    -- D84: re-pointing a borrow binding ends its old borrow; inside a side of `Id` that is a
    -- re-pointing ([Id-typestate] compares it, [Obs-ref] observes it), not an ending
    let o := (← get).obsFrame
    modify fun s => { s with obsFrame := none }
    endBorrow fuel' l
    modify fun s => { s with obsFrame := o }
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
is a value in flight (a block or a function may not return a borrow of its own local). D106:
the drop ends no borrow a value in flight holds; the borrows it ends with an access do so through
`endTopLoan`, which rejects that, and the check in `endLoansOfTopBind` is the same condition,
made before the access with the drop's own message. -/
def dropTopBind (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f ← topIdx
  let some b := (← get).env[f]!.binds.back? | err "internal: no binding to drop"
  -- D111: a borrow is a whole position's value (D48); a frame's pop drops its bindings here too
  if b.val.borrowBelowRoot then
    err s!"INTERNAL [Drop] {b.hint.name} holds a borrow below its root (D111: a borrow is a whole position's value; please report)"
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
    | _ => endTopLoan fuel' l "dropBind"; endLoansOfTopBind fuel' f
  | [] => pure ()
termination_by structural fuel

/-- [Drop] a discarded value (`t; u`), held with its type `T` as its evaluation returned it (D104). -/
def dropValue (fuel : Nat) (v : Value) (T : Option Value) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pushTemp v T "dropValue"
  -- D111: a borrow is a whole position's value (D48)
  if v.borrowBelowRoot then
    err s!"INTERNAL [Drop] a discarded value holds a borrow below its root (D111: a borrow is a whole position's value; please report)"
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
    | _ => endTopLoan fuel' l "dropTemp"; endLoansOfTopTemp fuel'
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

/-- The type of a place, read off the stored types (RULES §5; e1 F9), never off a value: every
binding has its declared type (D82). A total query: `none` only for an unknown slot of a
checker-internal frame (`⊥`, never read), an error when the place is ill-formed at the type it has. -/
def placeType? (fuel : Nat) (p : Place) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match p with
  | .var i =>
    let pos ← varPos i
    -- D82: a binding's type is its stored type, its declared type; never read off its value
    bindTy? fuel' pos
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
  | .proj i q => match ← placeType? fuel' q with
    | none => pure none
    | some .tNat =>     -- a Nat's `.0` is its predecessor (the built-in `S v`)
      if i == 0 then pure (some .tNat) else err s!"{← ppPlace q}.{i}: a number has no field {i} (its `.0` is its predecessor)"
    | some (.tInd n _) =>
      -- D81: field `i` of the type's one constructor, the place its pattern variable names
      let d ← lookupInd n
      if d.declaring then err (d.declaringMsg s!"{← ppPlace q}.{i}")
      let [(_, fields)] := d.ctors
        | err s!"{← ppPlace q}.{i}: {n} has {d.ctors.length} constructors, and `.{i}` names a field of a type with exactly one (use match)"
      let some (fname, _) := fields[i]?
        | err s!"{← ppPlace q}.{i}: the constructor of {n} has {fields.length} fields"
      placeType? fuel' (.field ⟨n, 0, i, fname⟩ q)
    | some T => err s!"{← ppPlace q}.{i}: no field {i} at type {T}"
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

/-- Whether a place holds a number, by its type (D82: every binding has its declared type). -/
def natPlace (fuel : Nat) (q : Place) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pure ((← placeType? fuel' q) == some .tNat)
termination_by structural fuel

/-- D81: the root-most step `q.i` of `p` whose parent `q` is not a number (a number's `.0` is
its predecessor, a sub-place of the built-in `S v`), with `p` as a function of the place that
replaces that step. -/
def projIn (fuel : Nat) (p : Place) : M (Option (Place × Nat × (Place → Place))) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match p with
  | .var _ => pure none
  | .deref q => pure ((← projIn fuel' q).map fun (r, i, k) => (r, i, fun x => .deref (k x)))
  | .field g q => pure ((← projIn fuel' q).map fun (r, i, k) => (r, i, fun x => .field g (k x)))
  | .proj i q =>
    if let some (r, j, k) ← projIn fuel' q then return some (r, j, fun x => .proj i (k x))
    if ← natPlace fuel' q then return none
    pure (some (q, i, id))
termination_by structural fuel

/-- D81 [Proj]: `q.i`, where `q`'s type is a declared inductive with one constructor `C`, is the
pattern variable `yᵢ` of `match q { C(y₀, …, yₙ) => … }`. A term `k(q.i)` runs as that match, its
one arm `k(q.g)` with `g` the constructor's field `i`: what the destructuring `let C(y₀, …, yₙ) = q`
does, a match by type on a proof (D45), [Split] on an unknown, the constructor of a value. `q.i`
has `q`'s class, a field of a proof being a proof and a field of data data, as the erasure pre-pass
reads it (`placeDecl`). -/
def projMatch (fuel : Nat) (q : Place) (i : Nat) (k : Place → Term) : M (Place × String × List (Hint × Term)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let pq ← ppPlace q
  -- the inductive: the head of `q`'s type (D82: every binding has its declared type)
  let n? ← match ← placeType? fuel' q with
    | some (.tInd n _) => pure (some n)
    | _ => pure none
  let some n := n?
    | err s!"{pq}.{i}: {pq} is not known to be of an inductive type (`.{i}` names a field of a type with one constructor)"
  let d ← lookupInd n
  if d.declaring then err (d.declaringMsg s!"{pq}.{i}")
  let [(cn, fields)] := d.ctors
    | err s!"{pq}.{i}: {n} has {d.ctors.length} constructors, and `.{i}` names a field of a type with exactly one (use match)"
  let some (fname, FT) := fields[i]?
    | err s!"{pq}.{i}: the constructor {cn} of {n} has {fields.length} fields"
  let fieldProof ← fieldTermIsProp d FT
  if d.sort == 0 && !fieldProof then err s!"{pq}.{i}: {subsingletonMsg d}"
  if d.sort != 0 && fieldProof then
    err s!"[D81] {pq}.{i}: field {fname} of {n} is a proof and {pq} is data, and `.{i}` takes a field of its parent's class: name it with a match, `let {cn}(…) = {pq}`"
  fire .Proj fun _ => s!"{pq}.{i} is the field {fname} of {cn}"
  pure (q, n, [(⟨cn⟩, k (.field ⟨n, 0, i, fname⟩ q))])
termination_by structural fuel

/-- D64, rule 2 and [Open]: the type of field `g` of the value at `q`, of the dependent
constructor `g.ctor` of `d` at parameters `ps`. Its type by the telescope is computed from
the earlier fields' current contents. A field whose declared type mentions no earlier field
has that type. Any other field has it while its content does (the value is packed);
otherwise the value is *open*, and the field is typed by its content's own type (what was
written into it, a stored type), until the value is repacked. -/
def depFieldType (fuel : Nat) (d : IndDecl) (ps : List Value) (g : FieldRef) (q : Place)
    (declared : Bool := false) : M Value := do
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
  if declared || !d.fieldDependent g.ctor g.idx then return T
  -- D112 amended: a mark (`lent_g`, a place lent to a borrow a call returned) is the content it
  -- marks, for typing as for paths and the repack (`lentUnknown`)
  let c := (fs.getD g.idx .bot).unmark
  -- a moved field has its declared type (any read of it is an error)
  if c == .bot then return T
  -- D110: a proof field holds `⋆` at its declared type; a data field never holds a proof (a strong
  -- update stores none), so it is not given a declared type it was never checked against
  if c == .proof then
    if ← fieldIsProof g then return T
    -- D112: a leaf field whose type computes to a proposition holds `⋆` at it (checked when assigned)
    if ← fieldIsLeaf fuel' d g.ctor g.idx then return T
    err s!"INTERNAL [Open] the data field {g.name} of {← ppPlace q} holds ⋆ (D110: a data field never holds a proof; please report)"
  -- D112: a leaf field is never typed by its content: it holds `⊥` or a value of its declared type
  -- at the current earlier fields (an index write invalidates it; an assignment is checked)
  if ← fieldIsLeaf fuel' d g.ctor g.idx then
    if (← packedErr fuel' c T).isNone then return T
    err s!"INTERNAL [Open] the leaf field {g.name} of {← ppPlace q} holds {c}, not of its declared type {T} (D112: an index write invalidates a leaf; please report)"
  if (← packedErr fuel' c T).isNone then return T
  -- D112: a tree field that does not fit its declared type is typed by its content, which (a
  -- strong update stores only a tree, D110/D112) always has a readable type
  let some S ← valType? fuel' c
    | err s!"[Open] {← ppPlace q}.{g.name} holds {c}, whose type cannot be read, and it is not of its declared type {T}"
  fire .Open fun _ => s!"{g.name} is open: typed by its content, {S}, not {T}"
  pure S
termination_by structural fuel

/-- D110: the declared type of the field place `p`, a field of a dependent constructor, at the
current contents of the earlier fields: what a write that is not a strong update is checked
against (`depFieldType` without [Open]'s reading of an open field by its content). -/
def fieldDeclType (fuel : Nat) (p : Place) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .field g q := p | placeType fuel' p
  match ← placeType? fuel' q with
  | some (.tInd n ps) => depFieldType fuel' (← lookupInd n) ps g q (declared := true)
  | _ => placeType fuel' p
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
  -- D112 amended: a mark is checked as the content it marks
  | .gloan _ w => packedErr fuel' w T
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

/-- The type of an embedded value (D82: never a binding's; census class (c)). A total
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
  | .clo cs (.fix _ hs ds c _ _) rd => pure (some (.tPi cs (.pi hs ds c) rd))
  | .borrow _ w => pure ((← valType? fuel' w).map .tRef)
  | .ind t c _ ps fs => if ps.isEmpty then indValType? fuel' t c fs else pure (some (.tInd t ps))   -- D49 (4)
  | .tNat | .tUnit | .tEq .. | .tRef _ | .tPi .. | .sort _ | .tInd .. =>
    pure (some (.sort (← sortOf fuel' v)))
  | .sealed t =>
    sealedType? fuel' t
  -- D112 amended: a mark is its content's type, as a loan is its borrow's content's
  | .gloan _ w => valType? fuel' w
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
def sealedType? (fuel : Nat) (t : Term) : M (Option Value) := privately do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D97: a program whose text holds a loan (a fill over a live borrow, met by [Repack] at a
  -- whole-again point) is not run: its type is read off its text, as [Close] wrote it. A fill
  -- reads a cell (`peek(c)`), of the type the cell was declared at (`(u : T)`) or of its initial
  -- value; a borrow result reads through the call's result, of its declared codomain's content;
  -- a result form is its head's declared codomain (`sealedResultType?`). Anything else: unknown.
  -- exp-block-text: a sealed block's text is never typed by running it either (its match would be
  -- split and closed off again): its type is read off its text, `B`, as recorded where it closed off
  if t.hasLoanAtom || t.isBlockText then
    let (bound, body) := t.letChain
    match body with
    | .prim "peek" [.place (.var i)] => match bound[i]? with
      | some (.ascribe (.val _) (.val T)) => return some T
      | some (.val u) => return ← valType? fuel' u
      | _ => return none
    | .prim "peek" [.place (.deref (.var i))] => match bound[i]? with
      | some c@(.call _ _ true) => return (match ← sealedResultType? fuel' c with | some (.tRef T) => some T | _ => none)
      | some (.block _ _ _ (.tRef T) _) => return some T
      | _ => return none
    | .call _ _ true => return ← sealedResultType? fuel' t
    | .block _ _ _ B _ => return some B
    | _ => return none
  -- outside the enclosing functions' checks for [Rec]'s test, but they are still being checked:
  -- D135 still keeps their bodies from running (`underCheck`)
  modify fun s => { s with env := #[{}], obsFrame := none, goal := none,
                           recStack := s.recStack.map ({ · with tests := false }) }
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
        -- D82: each parameter at its declared type, evaluated with the earlier ones bound
        pushBind h (some (← evalType fuel' PT)) v pd'.isProof pd'
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
`fs` (rule 2: a field's type is computed from the earlier fields' contents). D117: the frame that
types a later field binds what each earlier field stands for (`resolveLoans`), not a lent field's
loan, which would be a second occurrence of it whose read there ends the index's borrow. -/
def fieldTypesOf (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) (fs : List Value)
    (upto : Option Nat := none) : M (List (String × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  pure ((← fieldTele fuel' d ps c (fun j _ => resolveLoans fuel' (fs.getD j .bot)) upto).map fun (f, T, _) => (f, T))
termination_by structural fuel

/-- D64: fresh generic values for the fields of constructor `c`, each of its type computed
from the earlier ones ([Ind] and [Split]: `σ := C(σ₁, σ₂)` with `σ₂ : T₂[σ₁]`); a proof
field is `⋆`. Returns each field's name, type and value. -/
def fieldsGeneric (fuel : Nat) (d : IndDecl) (ps : List Value) (c : Nat) :
    M (List (String × Value × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  fieldTele fuel' d ps c fun _ T => genericValue fuel' T
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
  -- D82: each known slot at its declared type, evaluated where the declaration wrote it; an
  -- unknown slot is `⊥` with no type, and the guard above makes sure `FT` never reads one
  let known (j : Nat) : Bool := (j < np && (sol[np - 1 - j]!).isSome) ||
    (np ≤ j && j < np + k && np + k - 1 - j < earlier.length)
  privately do
    pushFrame
    for jj in [0:k] do pushBind ⟨(fields[jj]!).1⟩ none (earlier.getD jj .bot)
    for (((h, PT), v), i) in (d.params.zip sol.toList).zipIdx do
      let A ← if v.isSome && PT.freeVars.all (fun j => j < i && (sol[i - 1 - j]!).isSome)
        then some <$> evalType fuel' PT else pure none
      pushBind h A (v.getD .bot) false (← withLive true (typeDecl fuel' false [] [] PT))
    let top ← topIdx
    for jj in [0:earlier.length] do
      let some (_, FTj) := fields[jj]? | pure ()
      -- field `jj`'s type mentions the parameters and the fields before it, in this frame
      if FTj.freeVars.all known then
        let A ← evalType fuel' FTj
        modifyFrame top fun fr => { fr with binds := fr.binds.modify jj ({ · with ty := some A }) }
    some <$> evalType fuel' FT
termination_by structural fuel

/-- The type of a constructor value (for untyped bindings): its parameters are inferred
from its fields' types; a parameter no field determines (the `A` of `Nil`) is unknown. -/
def indValType? (fuel : Nat) (t : String) (c : Nat) (fs : List Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let d ← lookupInd t
  if d.declaring then err (d.declaringMsg s!"a value of {t}")
  if d.params.isEmpty then return some (.tInd t [])
  let some (_, fields) := d.ctors[c]? | err s!"{t} has no constructor {c}"
  let mut sol := Array.replicate d.params.length none
  for (v, (_, FT)) in fs.zip fields do
    let some T ← valType? fuel' v | return none
    -- D105: only where the parameters are inferred from it, as `evalCtor` infers them
    sol := unifyParams d.params.length (← inferFrom fuel' FT) T sol
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
        | .deref => .deref acc | .proj i => .proj i acc
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
  let .tPi cs (.pi hs ds c) rd := T | err s!"{T} is not a Π-type"
  privately do
    pushFrame
    pushCaps fuel' cs rd
    let (pds, _) ← paramDecls fuel' cs rd hs ds c
    let mut l := 0
    for ((d, h), pd) in (ds.zip hs).zip pds do
      let A ← evalType fuel' d
      l := max l (← sortOf fuel' A)
      let gv ← genericValue fuel' A pd
      let pd' ← refineDecl pd
      pushBind h (some A) gv pd'.isProof pd'
    let lb ← sortOf fuel' (← evalType fuel' c)
    pure (if lb == 0 then 0 else max l lb)
termination_by structural fuel

/-- Evaluate a type (P2: once, against the current Ω, on a private copy). -/
def evalType (fuel : Nat) (t : Term) : M Value := inStatement do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (v, T) ← eval fuel' true t
  match T with
  | some (.sort _) => pure v
  | some T => err s!"{t.pp []} is not a type (it has type {T})"
  | none => pure v
termination_by structural fuel

/-- Close a `pi`/`fix` term over the current values of its free variables (P2: a
Π-type is a closure over formation-time values, like a λ). Captured values are copied;
closures capture no borrows (RULES §1). Each capture is recorded with what its binding's
declared type says (D51, D80: the closure's body reads it so, as copy or not, on every path),
and with that declared type itself, its binding's stored type (D82: the closure's body runs with
every binding typed by declaration). -/
def capture (fuel : Nat) (t : Term) : M (List Value × Term × List (DeclInfo × Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let fvs := (t.freeVars.toArray.qsort (· > ·)).toList   -- oldest binding first
  let m := fvs.length
  let mut vals := #[]
  let mut rd := #[]
  let top0 := (← get).env.back!
  for o in fvs do
    -- [Fix] captures no borrow, a stuck block's borrow parameter included (D63, rule-audit
    -- item 7)
    let b0 := top0.binds[top0.binds.size - 1 - o]!
    let p := Place.var o
    -- D82: its declared type (a deferred parameter type is evaluated here, where it is read)
    let T0 ← bindTy? fuel' (← varPos o)
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
        if let some T := T0 then
          repackCheck fuel' s!"a closure or Π-type captures {b0.hint.name}" v T
      vals := vals.push v
      let some T := T0
        | err s!"INTERNAL [Capture] {b0.hint.name} has no stored type (D82: every binding has its declared type; please report)"
      rd := rd.push (b0.decl, T)
      -- D53: a runtime closure moves the variables it captures whose types are not copies
      if !(v matches .proof) then
        if v.hasHole then err "[D53] a closure captures a place that was partly moved out"
        unless ← copyRead fuel' p do
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
      if let some (_, T) := rd[k]? then
        t' := t'.inlineReads (m - 1 - k) (.ascribe (.val .proof) (.val T)) 0
  relocate t t'     -- the editor: the rebuilt body keeps its source ranges
  pure (vals.toList, t', rd.toList)
termination_by structural fuel

-- ### Conversion (P1, v1.5 D30)

/-- Conversion: same normal form, where the normal form of a function value is the
observation of its generic call (its result and the final contents of the generic
owned places) plus its captured values (D30). Structural everywhere else. `⊥` is a value of its
own, "moved on every path" (D84): it is convertible with itself only. -/
def conv (fuel : Nat) (v w : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D103: a comparison keeps nothing but names. On every exit it puts back the state it started
  -- from, keeping only the fresh names made inside (`restoreNames`): its result is a boolean,
  -- which can mention nothing it made
  let saved ← get
  let r ← onFail (do
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
    | .tPi cs t r, .tPi ds u r' =>
      -- same captures, read alike, and code
      if r == r' && (← convList fuel' cs ds) && (← convT fuel' t u) then return true
      convPi fuel' v w
    | f, g =>
      let isFn : Value → Bool := fun | .gfn _ | .clo _ _ _ => true | _ => false
      if isFn f && isFn g then convFn fuel' f g else pure false
    ) (restoreNames saved)
  restoreNames saved
  pure r
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
  -- D103: a comparison keeps nothing but names. On every exit it puts back the state it started
  -- from, keeping only the fresh names made inside (`restoreNames`): its result is a boolean,
  -- which can mention nothing it made
  let saved ← get
  let r ← onFail (do
    let .tPi cs (.pi hs ds c) rd := P | return false
    let .tPi cs' (.pi _ ds' c') rd' := Q | return false
    if ds.length != ds'.length then return false
    -- D54: the erasure class, and whether it returns a borrow, are part of the Π-type (the
    -- `Unit` and data rows of [Close] may differ: `Unit` has one value, D54 refined)
    unless (← fnClass fuel' P) == (← fnClass fuel' Q) && ((← declKind fuel' P) == .ref) == ((← declKind fuel' Q) == .ref) do
      return false
    if (← get).convStack.contains (P, Q) then return false
    privately do
        modify fun s => { s with env := #[{}], obsFrame := none, convStack := (P, Q) :: s.convStack }
        pushFrame
        pushCaps fuel' cs rd
        let (pds, _) ← paramDecls fuel' cs rd hs ds c
        let mut ws : Array (Value × Value) := #[]
        for ((d, h), pd) in (ds.zip hs).zip pds do
          let A ← evalType fuel' d
          let w ← match A with
            | .tRef T =>
              let c ← absAt fuel' pd.deref T
              let l ← freshLoan
              modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
              pure (Value.borrow l c)
            | _ => genericValue fuel' A pd
          let pd' ← refineDecl pd
          pushBind h (some A) w pd'.isProof pd'
          ws := ws.push (w, A)
        let C ← evalType fuel' c
        discard popFrameRaw
        -- D115: the generic arguments are held in Ω, temporaries of frame 0, while `Q`'s parameter
        -- types are evaluated, until its frame binds each (taking a borrow from its temporary)
        for (w, A) in ws do pushTemp w (some A) "convPi"
        pushFrame
        pushCaps fuel' cs' rd'
        let (pds', _) ← paramDecls fuel' cs' rd' hs ds' c'
        for (((d', h), (w, A)), pd) in ((ds'.zip hs).zip ws.toList).zip pds' do
          let A' ← evalType fuel' d'
          unless ← conv fuel' A A' do return false
          let pd' ← refineDecl pd
          takeArgBorrow w
          pushBind h (some A') w pd'.isProof pd'
        let C' ← evalType fuel' c'
        conv fuel' C C'
    ) (restoreNames saved)
  restoreNames saved
  pure r
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
  | .succ a, .succ b | .ref a, .ref b => convT fuel' a b
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
  -- exp-block-text: two sealed blocks, by their texts (cells, declared types read alike, type,
  -- match), embedded values by `conv`; a block is not a function, so never by observation
  | .block cs rd pf B m, .block ds rd' pf' B' m' =>
    pure (pf == pf' && rd.map (·.1) == rd'.map (·.1) && (← convTList fuel' (cs.map (·.2)) (ds.map (·.2)))
      && (← convList fuel' (rd.map (·.2)) (rd'.map (·.2))) && (← conv fuel' B B') && (← convT fuel' m m'))
  | _, _ => pure false
termination_by structural fuel

/-- Two function values: compare their Π-types, their captured values, and the
observations of their generic calls, run from one shared generic environment. A
comparison that needs itself again (a recursive function stuck at its own generic
call observes only a sealed call of itself) answers "not convertible": sound, and
incomplete only for functions whose observation mentions themselves. -/
def convFn (fuel : Nat) (f g : Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D103: a comparison keeps nothing but names. On every exit it puts back the state it started
  -- from, keeping only the fresh names made inside (`restoreNames`): its result is a boolean,
  -- which can mention nothing it made
  let saved ← get
  let r ← onFail (do
    if (← get).convStack.contains (f, g) then return false
    let pf ← funType fuel' f none
    let pg ← funType fuel' g none
    unless ← conv fuel' pf pg do return false
    let caps : Value → List Value := fun | .clo cs _ _ => cs | _ => []
    unless ← convList fuel' (caps f) (caps g) do return false
    let .tPi cs (.pi hs ds c) _ := pf | return false
    -- a comparison that errors (e.g. a stuck block's function run at a generic argument where
    -- a pattern's sub-place does not exist, fuzz-port R3) is an error, as in `convPi`
    convFnRun fuel' f g pf cs hs ds c
    ) (restoreNames saved)
  restoreNames saved
  pure r
termination_by structural fuel

/-- `convFn`'s observation of both functions' generic calls. -/
def convFnRun (fuel : Nat) (f g pf : Value) (cs : List Value) (hs : List Hint) (ds : List Term) (c : Term) :
    M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  privately do
    modify fun s => { s with env := #[{}], obsFrame := none, convStack := (f, g) :: s.convStack }
    pushFrame
    let rd := match pf with | .tPi _ _ rd => rd | _ => []
    pushCaps fuel' cs rd
    let (pds, cd) ← paramDecls fuel' cs rd hs ds c
    let mut args := #[]
    let mut argTys := #[]
    for ((d, h), pd) in (ds.zip hs).zip pds do
      let A ← evalType fuel' d
      let w ← match A with
        | .tRef T =>
          let c ← absAt fuel' pd.deref T
          let l ← freshLoan
          modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
          pure (Value.borrow l c)
        | _ => if ← isPropV fuel' A then pure Value.proof else absAt fuel' pd A
      let pd' ← refineDecl pd
      pushBind h (some A) w pd'.isProof pd'
      args := args.push w
      argTys := argTys.push (some A)
    discard popFrameRaw
    -- D115: the generic arguments leave the frame that typed them for the temporaries of frame 0,
    -- where they are held, at their types, through the result's type and both observations
    for (w, A) in args.zip argTys do pushTemp w A "convFnRun"
    -- D38 (v1.8): a borrow result is observed as its content, after one shared fresh
    -- value is written through it, so the owners show where it points
    let σw? ← match pf with
      | .tPi _ (.pi _ _ (.ref _)) _ =>
        match ← callType fuel' pf args (args.map fun _ => none) with
        | .tRef T => some <$> freshAbsR fuel' T
        | _ => pure none
      | _ => pure none
    -- D80: the generic call's static readings are `pf`'s: its codomain's, and its borrow
    -- parameters' (for [Close]'s fills)
    let fills := pds.toArray.map (· == .ref .unit)
    let obs (fv : Value) : M (Value × List Value) := privately do
      -- D115: the call holds its head below its arguments: the arguments are taken off and pushed
      -- again above the head (the head at its own Π-type, which conversion has already compared),
      -- with nothing run in between
      let fT ← funType? fuel' fv none
      let ws ← popTemps args.size
      pushTemp fv fT "convFnRun"
      for (w, A) in ws.zip argTys do pushTemp w A "convFnRun"
      let (r, R) ← callFn fuel' false none args.size (args.map fun _ => none) false (res := cd) (fills := fills)
      wholeReturned r
      let r' ← obsResult fuel' r R σw?
      pure (r', (← get).env[0]!.binds.toList.map (·.val))
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
`False` (v2.0, D47), and so are `⊥` and a value (D84). Proofs are all `⋆`, so an equation
between proofs is reflexive. -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 17): `Eq` computes on values: reflexive by conversion (closed under refinement), injective and disjoint on constructor heads and `⊥` (which refinement keeps; D84: `⊥` is definite), stuck otherwise.
def mkEqM (fuel : Nat) (A a b : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D84: `⊥` means moved on every path (a match drops at its join what any arm moves), so it is a
  -- value of its own: equal to itself ([Eq-refl]) and distinct from every other value
  -- ([Eq-disj]): an abstract value or a sealed program stands for a value, never for a moved
  -- place. Inside a constructor, injectivity reaches it
  if (a == .bot) != (b == .bot) then
    fire .EqDisj fun _ => s!"{a} and {b}: ⊥ against a value"
    return vFalse
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
    let σ ← freshAbsR fuel' A
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
  located t (noteValue t (evalAt fuel' typed t hint)) (flight := some) (ownTyping := some typed)
termination_by structural fuel

def evalAt (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let before := (← get).env
  -- the erasure pre-pass: decided before the term runs, from declared types (a call's
  -- head is not classified: its flags are the call's)
  let head := (← get).headEval
  let hinted := (← get).tailDecl     -- a sequencing form hands its reading to its tail
  -- D82: whether this term's context reads its type (always, in typing)
  let want := typed || (← get).wantTy
  let wantHere0 := (← get).wantHere
  -- static ends: whether this term is in tail position of the body being run (one-shot)
  let tail := (← get).tailNext
  -- D130: whether this term is a `let`'s right-hand side call whose type is deferred (one-shot), and
  -- the record of a deferred call's type, which only the call this evaluation makes may leave
  let defer := (← get).deferCallTy
  modify fun s => { s with headEval := false, tailDecl := none, wantTy := false, wantHere := want,
                           deferCallTy := false, deferHere := defer, callTyLater := none }
  modify fun s => { s with tailNext := false, curTail := tail }
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
  -- (E1, `inStatement`: the one place a statement position runs)
  let erasedHere := pre matches some (true, _)
  let r ← onFail (if erasedHere then do
        -- the classification flags the term set are its own, not the copy's
        let (r, fl) ← inStatement (do let r ← evalCore fuel' typed t hint; pure (r, ← getFlags))
        setFlags fl
        pure r
      else evalCore fuel' typed t hint)
    (modify fun s => { s with typing := typing0, wantHere := wantHere0 })
  modify fun s => { s with typing := typing0, wantHere := wantHere0 }
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
    | .block .. => getFlags        -- exp-block-text: set by `runBlock`, data (a proof block has no text)
    | .seq _ _ | .letIn _ _ _ | .matchNat _ _ _ | .matchInd _ _ _ =>
      let (_, p) ← getFlags
      pure (p, p)
    | .cong _ _ | .prim "trans" _ | .prim "symm" _ => pure (true, true)
    -- D116: `clone(p)` is what `p` is: its declared reading is its operand's (`Decide.declOf`), and
    -- a proposition is a copy (D100), so the clone of a proof is that proof, `⋆` flagged a proof,
    -- and of data a copy of the data (the operand's flags, set by its own evaluation)
    | .prim "clone" _ => getFlags
    -- D125: an untyped `split f in u` is `u` (the typed one is checked by `checkTailAt` only)
    | .prim "split" _ => getFlags
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

/-- D124, `J`: the motive `P` at the first endpoint's value `av`, `P(a)`, the type the typed check
hands the transported term (as its hint) and checks it against, computed as the typed check computes
it: `A` and `P` evaluated and `P` called at `av`, on a private copy (they are statements). -/
def jMotiveAt (fuel : Nat) (A P : Term) (av : Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  inStatement do
    let A' ← evalType fuel' A
    let (Pv, PT) ← eval fuel' true P
    -- D115: the call's head and argument are held in Ω, as temporaries, until it binds them
    pushTemp Pv PT "J"; pushTemp av (some A') "J"
    pure (← callFn fuel' true PT 1 #[some A'] false).1
termination_by structural fuel

/-- `hint`: the type the context requires of `t`, used only to infer the parameters of a
constructor application that its fields do not determine (v2.0, D46). -/
def evalCore (fuel : Nat) (typed : Bool) (t : Term) (hint : Option Value := none) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  tick
  -- static ends: this term's tail position, read before any nested `eval` sets it again
  let tail := (← get).curTail
  -- D82: the machine carries types as typing does (every binding has its declared type); it
  -- differs from typing only where a run is stuck (it closes off where typing splits) and in
  -- not re-checking the code it runs (the checks below are typing's). It computes a term's type
  -- only where its context reads it (`want`: a `let`'s right-hand side, a borrow argument, a
  -- call's head, and their tails), lazily; typing always does
  let want ← wanted
  let ty (T : Value) : Option Value := some T
  -- D81 [Proj]: a place operand with a field step `q.i` runs as the match on `q` that names it
  if let some (p, k) := t.placeOperand? then
    if let some (q, i, rebuild) ← projIn fuel' p then
      let (q, n, arms) ← projMatch fuel' q i (fun f => k (rebuild f))
      return ← evalMatchInd fuel' typed q n arms (tail := tail)
  match t with
  | .place p =>
    let T ← if typed then some <$> placeType fuel' p else if want then placeType? fuel' p else pure none
    if typed then if let some T := T then repackAt fuel' p T "read whole"
    pure (← readPlace fuel' p, T)
  | .borrow p =>
    let T ← if typed then some <$> placeType fuel' p else if want then placeType? fuel' p else pure none
    if typed then if let some T := T then
      if T.typeHasRef then err s!"&{← ppPlace p}: a borrow of a borrow-typed place"
      -- D66 for terms ([T-Borrow]'s premise, reviewer-6's A12): the borrowed place's type
      -- is in Type₀, as for the type former `&A`
      if !(← isBorrowable fuel' T) then
        err s!"[D66] &{← ppPlace p}: its type {T} is not in Type₀ (only runtime types are borrowed: never a proposition, Prop, a universe, or a type not known to be in Type₀)"
      repackAt fuel' p T "borrowed whole"
    let b ← borrowPlace fuel' p
    -- D115: the new borrow is held in Ω, a temporary at its type, while the write through an
    -- index field invalidates (`openWrite` accesses the leaf fields its type mentions)
    pushTemp b (T.map .tRef) "borrow"
    openWrite fuel' p
    pure (← popTemp, T.map .tRef)
  | .assign p u =>
    if typed then
      if let some r ← lentProofAssign fuel' p u then return r
    -- the place's type is the type the context requires of a constructor's parameters and of an
    -- embedded value with no type of its own (an inert loan in a sealed program's `*r := loan`)
    -- D124: in the untyped run too, at the same forms (the typed check's decision, from syntax)
    let hint ← if (u matches .ctor .. | .val _) && (typed || (← readsHint fuel' false false u)) then
        placeType? fuel' p
      else pure none
    -- the place's type, read before the value is evaluated: evaluating it may move the place's
    -- content out (`*x := match *x {…}`, D68)
    let Tp0 ← if typed then placeType? fuel' p else pure none
    -- D64 [Open]: a field whose declared type mentions earlier fields takes any value (a strong
    -- update: while its value is open it is typed by what it holds); [Repack] checks it later.
    -- D110: only a value whose declared type reads as first-order data (`Decide.strongStorable`);
    -- any other is checked against the field's declared type at the current earlier fields
    let strong ← if typed then strongUpdate p else pure false
    let storable ← if strong then pure (strongStorable (← withLive true (declOf fuel' false [] [] u))) else pure false
    let Td0 ← if strong && !storable then some <$> fieldDeclType fuel' p else pure none
    let (v, Tv) ← eval fuel' typed u hint
    -- D115: the value is held in Ω, a temporary at its type, while it is checked and stored
    pushTemp v Tv "assignPlace"
    -- [Open]: a strong update
    if strong && storable then fire .Open fun _ => s!"a strong update of a dependent field, to a value of type {Tv.getD .bot}"
    if typed && !(strong && storable) then
      -- D112: a leaf field assigned while part of its value is lent is checked with what the
      -- borrows hold unknown, as a proof field is (`lentLeafCheck`)
      unless ← lentLeafCheck fuel' p Tv do
        expectTy fuel' "the assigned value" Tv (← match Td0, Tp0 with
          | some T, _ | none, some T => pure T
          | none, none => placeType fuel' p)
    assignPlace fuel' p
    openWrite fuel' p
    pure (.unit, ty .tUnit)
  | .letIn h u w =>
    let myD := (← get).curDecl
    let du ← withLive true (declOf fuel' false [] [] u)
    demand true      -- D82: `h` is bound at its right-hand side's type
    -- D132: an untyped run defers the type of a right-hand side that is a call the pre-pass does not
    -- erase. An erased call (one returning a type or a proof) runs as a statement on a private copy
    -- (`evalAt`), which would discard the record of its deferred type with the copy and leave `h`
    -- with no type; not deferred, its type is computed inside the statement and comes back with its
    -- value. Decided from `u`'s declared reading, as `evalAt` decides the statement (`preFlags`)
    let callU := !typed && (u matches .call _ _ _)
    let erasedU ← if !callU || du matches .conflict then pure false
      else pure (((← preFlags u du).map (·.1)).getD false)
    let isCall := callU && !erasedU
    -- D130: the flag is consumed when `u`'s evaluation starts, which also clears the record
    if isCall then modify fun s => { s with deferCallTy := true }
    let (v, T) ← eval fuel' typed u
    let later0 := (← get).callTyLater
    let later := if isCall && T.isNone then later0 else none
    modify fun s => { s with callTyLater := none }
    let du' ← refineDecl du
    -- `h` is a proof iff `u` is, or its declared type is a proposition (P1; `u` may be an
    -- embedded value, `⋆` in a sealed program's bindings, which the pre-pass does not read)
    let p := (← getFlags).2 || du'.isProof
    -- D131: in a typed run the binding's reading agrees with its type
    if typed then if let some T' := T then readingAgrees fuel' h T' du' v
    pushBind h T v p du'
    -- D82: a call's type, the declared codomain at its arguments, evaluated when it is read
    if let some (P, ws) := later then
      if let Value.tPi _ (.pi _ ds _) _ := P then
        modifyFrame (← topIdx) fun fr =>
          { fr with binds := fr.binds.modify (fr.binds.size - 1) ({ · with lazyTy := some (P, ws, ds.length) }) }
    -- the tail's reading is this let's (read with `h`'s declared type, unless refined)
    if du' == du then modify fun s => { s with tailDecl := myD }
    demand want
    modify fun s => { s with tailNext := tail }     -- static ends: the body is the let's tail
    -- D89: the tail's hint; D124: only in tail position, where the typed check hands it the goal
    let (r, R) ← eval fuel' typed w (if typed || !tail then none else hint)
    let fl ← getFlags     -- the body's erasure flags (dropping may normalise)
    pushTemp r R "letIn"
    dropTopBind fuel'
    setFlags fl
    pure (← popTemp, R)
  | .seq u w =>
    let myD := (← get).curDecl
    let (v, Tv) ← eval fuel' typed u
    dropValue fuel' v Tv
    modify fun s => { s with tailDecl := myD }     -- the tail's reading is this sequence's
    demand want
    modify fun s => { s with tailNext := tail }     -- static ends: the tail is the sequence's
    eval fuel' typed w (if typed || !tail then none else hint)     -- D124: as a `let`'s tail
  -- D124: an untyped match hands its arms the hint only in tail position, as the typed check does
  | .matchNat p z s => evalMatch fuel' typed p z s (if typed || !tail then none else hint) (tail := tail)
  | .matchInd p ty arms => evalMatchInd fuel' typed p ty arms (if typed || !tail then none else hint) (tail := tail)
  | .tind n as => evalTInd fuel' typed n as
  | .ctor ty c h ps as => evalCtor fuel' typed ty c h ps as hint
  | .const n =>
    let g ← lookupGlobal n
    let v ← if ← isPropV fuel' g.ty then pure .proof else pure g.val
    pure (v, some g.ty)
  | .val v =>
    -- an embedded value is typed by the position it was embedded at (the hint), as below
    let hint ← forceHint fuel' hint
    -- D124, an embedded value's type: the untyped run types it as the typed check does (below), by
    -- its kind (`valType?`: a number, an unknown, a constructor, a type, a closure, a sealed program,
    -- a live loan's content) and else by the hint (a proof; a loan whose borrow is gone), where its
    -- context reads its type (`want`); where nothing reads it, it is not computed
    if !typed then
      if !want then return (v, hint)
      return (v, (← valType? fuel' v).orElse fun _ => hint)
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
    let (cs, t', rd) ← inStatement (capture fuel' t)
    let T := Value.tPi cs t' rd
    if !typed then return (T, ← if want then (some ∘ Value.sort) <$> sortOf fuel' T else pure none)
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
    -- D78: the captured bindings' [Rec] marks, read before `capture` moves them
    let capRec ← capMarks t
    let (cs, t', rd) ← capture fuel' t
    let v := Value.clo cs t' rd
    let T := match t' with
      | .fix _ _ ds' c' _ _ => Value.tPi cs (.pi hs ds' c') rd
      | _ => Value.tPi cs (.pi hs ds c) rd
    if typed then checkFix fuel' v cs t' capRec rd
    let v ← if ← isPropV fuel' T then pure .proof else pure v
    pure (v, some T)
  | .call f as hd => evalCall fuel' typed f as hd
  | .block cs rd pf B m => runBlock fuel' typed cs rd pf B m
  | .nat => pure (.tNat, some (.sort 1))
  | .unit => pure (.tUnit, some (.sort 1))
  | .zero => pure (.zero, ty .tNat)
  | .tt => pure (.unit, ty .tUnit)
  | .succ u =>
    let (v, T) ← eval fuel' typed u
    if typed then expectTy fuel' "the argument of S" T .tNat
    pure (.succ v, ty .tNat)
  | .eq A a b => inStatement do
    -- each side is a statement position: it runs on its own private copy of the state, so
    -- its effects are visible to the rest of that side and to nothing else (one copy per side)
    let A' ← evalType fuel' A
    let (va, Ta) ← inStatement (eval fuel' typed a)
    let (vb, Tb) ← inStatement (eval fuel' typed b)
    if typed then
      expectTy fuel' "the left side of Eq" Ta A'
      expectTy fuel' "the right side of Eq" Tb A'
    pure (← mkEqM fuel' A' va vb, some (.sort 0))
  | .cong f h =>
    demand want
    let (fv, fT) ← eval fuel' typed f
    demand want
    let (_, Th) ← eval fuel' typed h
    if !want then return (.proof, none)
    match Th.map unitTop with
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    | some (.tEq A a b) =>
      -- D80: `f`'s declared codomain, as at any call of `f`
      let res := match ← withLive true (declOf fuel' false [] [] f) with
        | .pi r => r
        | _ => .other
      -- D115: each call's head and argument are held in Ω, as temporaries, until it binds them
      pushTemp fv fT "cong"; pushTemp a (some A) "cong"
      let (fa, B) ← callFn fuel' true fT 1 #[some A] false (res := res)
      pushTemp fv fT "cong"; pushTemp b (some A) "cong"
      let (fb, _) ← callFn fuel' true fT 1 #[some A] false (res := res)
      pure (.proof, some (← mkEqM fuel' B.get! fa fb))
    | some T => if typed then err s!"cong: the proof has type {T}, which is not an equation" else pure (.proof, none)
    | none => if typed then err "cong: untyped proof" else pure (.proof, none)
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
      -- D85 [J-run]: in the erased program `J` is `t`, unconditionally. Its endpoints, motive
      -- and proof are statements, which the erased program does not have, so nothing is run or
      -- compared. A mode of the run (`MState.runtime`), set only by the runtime's entry point
      -- (`Ochr/Runtime.lean`), never by the checker, whose untyped runs keep [J] and [J-stuck]
      if (← get).runtime then
        fire .JRun
        -- D84 [Join]: `t` is the one arm, at the join's grain, as at every other run of `J`
        -- static ends, rule 2: its entry ends what [T-J-stuck]'s block would
        discard (blockEntry fuel' u)
        return ← joinDrop fuel' t (do demand want; eval fuel' false u)
      -- D124: `t`'s hint is `P(a)`, as on both typed paths, computed only where `t` reads it
      -- (`readsHint`: not in tail position), as the typed check computes it (`jMotiveAt`)
      let reads ← readsHint fuel' false false u
      if !(← jErased fuel' P) then
        -- its endpoints are erased positions, on private copies; `A` and `h` are never run by
        -- the machine (A.191), nor `P` but for `t`'s hint
        let (av, _) ← inStatement (eval fuel' false a)
        let (bv, _) ← inStatement (eval fuel' false b)
        -- [J]: the endpoints are convertible, `J` is `t`; [J-stuck]: otherwise the run is
        -- stuck, and `t` does not run (D56, D63, rule-audit item 5)
        -- D84 [Join]: `t` is the one arm, so its moves are taken at the join's grain
        -- static ends, rule 2: its entry ends what [T-J-stuck]'s block would
        if ← conv fuel' av bv then
          let hJ ← if reads then some <$> jMotiveAt fuel' A P av else pure none
          discard (blockEntry fuel' u)
          return ← joinDrop fuel' t (do demand want; eval fuel' false u hJ)
        stuckNow
      let hJ ← if reads then some <$> jMotiveAt fuel' A P (← inStatement (eval fuel' false a)).1 else pure none
      demand want
      return (← eval fuel' false u hJ)
    let A' ← evalType fuel' A
    let (av, Ta) ← inStatement (eval fuel' true a)
    let (bv, Tb) ← inStatement (eval fuel' true b)
    expectTy fuel' "J's first endpoint" Ta A'
    expectTy fuel' "J's second endpoint" Tb A'
    let (Pv, PT) ← inStatement (eval fuel' true P)
    let (_, Th) ← eval fuel' true h
    let hT ← mkEqM fuel' A' av bv
    expectTy fuel' "J's equation" Th hT
    -- D115: each call's head and argument are held in Ω, as temporaries, until it binds them
    pushTemp Pv PT "J"; pushTemp av (some A') "J"
    let (Pa, _) ← callFn fuel' true PT 1 #[some A'] false
    pushTemp Pv PT "J"; pushTemp bv (some A') "J"
    let (Pb, _) ← callFn fuel' true PT 1 #[some A'] false
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
    -- static ends, rule 2: its entry ends what [T-J-stuck]'s block would
    discard (blockEntry fuel' u)
    -- D124: `t` gets the hint `P(a)`, as where `J` is stuck (above): the two typed paths hand it the same
    let (v, Tu) ← joinDrop fuel' t (eval fuel' true u (some Pa))
    let fl ← getFlags
    expectTy fuel' "the transported term" Tu Pa
    setFlags fl    -- t's flags (J is t)
    pure (v, some Pb)
  | .prim "symm" [h] =>
    demand want
    let (_, Th) ← eval fuel' typed h
    match Th.map unitTop with
    | some (.tEq A a b) => pure (.proof, some (← mkEqM fuel' A b a))
    | some (.tInd "True" []) => pure (.proof, some vTrue)
    -- an equation that computes to `False` (a refinement made it impossible) is symmetric
    -- to one that does too (fuzz-port R7)
    | some (.tInd "False" []) => pure (.proof, some (.tInd "False" []))
    | _ => if typed then err "symm: not an equation" else pure (.proof, none)
  | .prim "trans" [h, k] =>
    demand want
    let (_, Th) ← eval fuel' typed h
    demand want
    let (_, Tk) ← eval fuel' typed k
    match Th.map unitTop, Tk.map unitTop with
    | some (.tInd "True" []), some T | some T, some (.tInd "True" []) => pure (.proof, some T)
    | some (.tInd "False" []), _ | _, some (.tInd "False" []) => pure (.proof, some (.tInd "False" []))
    | some (.tEq A a b), some (.tEq A' b' c) =>
      if (← conv fuel' A A') && (← conv fuel' b b') then pure (.proof, some (← mkEqM fuel' A a c))
      else if typed then err s!"trans: {Th.get!} and {Tk.get!} do not compose" else pure (.proof, none)
    | _, _ => if typed then err "trans: not equations" else pure (.proof, none)
  | .prim "rewrite" [h, u] | .prim "rewriteR" [h, u] =>
    -- D60 [Rewrite]: checked against the type the context requires (`hint`)
    let hint ← forceHint fuel' hint
    if !typed then return (.proof, hint)
    let some G := hint
      | err "rewrite: the goal is not known here (use it in tail position, as a call's argument, or under an annotation `let x : T = …`)"
    let G' ← rewriteGoal fuel' (t matches .prim "rewriteR" _) h G
    let (_, Tu) ← eval fuel' true u (some G')
    expectTy fuel' "the rewritten term" Tu G'
    pure (.proof, some G)
  | .prim "split" [_, u] =>
    -- D61: the typed check splits the goal at the end of a body (`checkTailAt`); a typed run
    -- elsewhere has no goal to split
    if typed then err "split: only in tail position (where the goal is known)"
    -- D125: the untyped run (a called body, a sealed program's re-run, the runtime) runs `u`, as
    -- a `let`'s tail: the split decides nothing a run needs, since `u` names the call it splits on
    -- (D126: `split f(ā) { arms }` is `split f in match f(ā) { arms }`) and a run computes it
    let myD := (← get).curDecl
    modify fun s => { s with tailDecl := myD }     -- the tail's reading is the split's
    demand want
    modify fun s => { s with tailNext := tail }     -- static ends: `u` is the split's tail
    eval fuel' false u (if tail then hint else none)     -- D124: the hint only in tail position
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
    pure (← if p then pure Value.proof else absOf fuel' G, some G)
  -- D53: `clone(p)` copies `p` (an erased read); `peek` is an observation's final read
  -- D122: both take a place, in the core as in the surface ("clone takes a place"): only a read of
  -- a place is run in copying mode. The checker builds neither of anything else (`capture`
  -- inlines `clone` of a captured proof as the proof itself, `Term.inlineReads`)
  | .prim "clone" [u] =>
    let .place p := u | err s!"[D122] clone takes a place: clone({u.pp []})"
    -- K2: cloning a view at runtime copies it
    if let some v ← content? p then unsizedCheck p v "cloned"
    demand want
    withCopying (withErased (eval fuel' typed u hint))
  | .prim "peek" [u] => do
    unless u matches .place _ do err s!"[D122] peek takes a place: peek({u.pp []})"
    demand want; withCopying (withErased (eval fuel' typed u hint))
  | .prim "inplace" [t] =>
    if t matches .place _ then modify fun s => { s with inPlace := true }
    demand want
    let r ← eval fuel' typed t hint
    modify fun s => { s with inPlace := false }
    pure r
  | .prim n _ => err s!"unknown primitive {n}"
  | .ascribe (.val .proof) A =>     -- a captured proof, inlined with its type (`capture`)
    if !typed && !want then return (.proof, none)
    pure (.proof, some (← evalType fuel' A))
  | .ascribe u A =>
    -- D82: an annotation is the term's declared type; the machine does not re-check it
    if !typed && !want then
      -- D89: the annotation is the hint of a constructor its fields do not determine; D124: it is
      -- the term's hint wherever the typed check hands it, which is always
      let h ← if ← readsHint fuel' false false u then some <$> evalType fuel' A else pure none
      return ((← eval fuel' false u h).1, none)
    let A' ← evalType fuel' A
    if !typed then return ((← eval fuel' false u (some A')).1, some A')
    let (v, T) ← match u with
      | .matchNat p z s => evalMatch fuel' true p z s (some A')
      | .matchInd p ty arms => evalMatchInd fuel' true p ty arms (some A')
      | _ => eval fuel' true u (some A')      -- the annotation is a hint for a constructor's parameters
    let fl ← getFlags
    expectTy fuel' "the ascribed term" T A'
    setFlags fl
    pure (v, some A')
termination_by structural fuel

/-- D64 amended, D112 ([Open]): the borrows that lend part of the value at `q`, a constructor value
of `g`'s constructor (a live loan in its fields). -/
def lentInFields (q : Place) (g : FieldRef) : M (List Nat) := do
  let cv := (← content? q).getD .bot
  let some fs ← ctorFields cv g | return []
  let env := (← get).env
  pure (fs.flatMap fun w => liveLoansIn env w).eraseDups

/-- D64 amended, D112 ([Open]): on the current (private) copy, each borrow in `ls` holds a fresh
abstract value of the type of what it holds now: whatever it may still write. -/
def unknownLent (fuel : Nat) (what : String) (ls : List Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for l in ls do
    let env := (← get).env
    let some pos := findBorrow env l | continue
    let some (c, _) := (valAt env pos).takeBorrow l | continue
    let some T ← valType? fuel' c
      | err s!"[Open] {what} is assigned while its value is lent, and the type of what the borrow holds ({c}) is not known"
    let σ ← absOf fuel' T
    setAt pos ((valAt env pos).setBorrowContent l σ)
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
  let ls ← lentInFields q g
  if ls.isEmpty then return none
  fire .Open fun _ => s!"the proof field {g.name} is assigned while borrows {ls} lend part of its value: checked with what they hold unknown"
  privately do
    unknownLent fuel' s!"the proof field {g.name}" ls
    let T ← placeType fuel' p
    let (_, Tv) ← eval fuel' true u (some T)
    expectTy fuel' s!"the proof assigned to {g.name} (while part of its value is lent, what the borrow holds unknown: [Open])" Tv T
  -- D104: no type is in hand here: the proof was checked on the private copy above, at the
  -- field's type there, where the lent parts were unknowns
  pushTemp .proof none "assignPlace"
  assignPlace fuel' p
  openWrite fuel' p
  pure (some (.unit, some .tUnit))
termination_by structural fuel

/-- D112 ([Open]): the assignment of a value of type `Tv` to the LEAF field `p` while part of its
value is lent (a live loan in its fields) is checked as a proof field's is (`lentProofAssign`):
against the field's declared type on a private copy in which each such borrow holds a fresh
abstract value of its type, since the borrow may still write there and nothing would invalidate
the leaf again. `false`: not this case (the ordinary [Assign] check applies). -/
def lentLeafCheck (fuel : Nat) (p : Place) (Tv : Option Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .field g q := p | return false
  let some d := (← get).inds.find? (·.name == g.ty) | return false
  unless ← fieldIsLeaf fuel' d g.ctor g.idx do return false
  let ls ← lentInFields q g
  if ls.isEmpty then return false
  fire .Open fun _ => s!"the leaf field {g.name} is assigned while borrows {ls} lend part of its value: checked with what they hold unknown"
  privately do
    unknownLent fuel' s!"the field {g.name}" ls
    let T ← fieldDeclType fuel' p
    expectTy fuel' s!"the value assigned to {g.name} (while part of its value is lent, what the borrow holds unknown: [Open])" Tv T
  pure true
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
  pure (.tInd n vs.toList, some (.sort d.sort))
termination_by structural fuel

/-- Parameters are type positions: each on a private copy (P2). -/
def evalParams (fuel : Nat) (n : String) (as : List Term) (typed : Bool) :
    M (Array Value × Array (Option Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let mut vs := #[]
  let mut tys := #[]
  for a in as do
    let (v, T) ← inStatement (eval fuel' typed a)
    vs := vs.push v
    tys := tys.push T
  pure (vs, tys)
termination_by structural fuel

/-- Each parameter against its declared type, evaluated with the earlier ones bound; no
borrow types (no borrows inside data). -/
def checkParams (fuel : Nat) (d : IndDecl) (n : String) (vs : Array Value) (tys : Array (Option Value)) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  privately do
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
  if d.declaring then err (d.declaringMsg s!"the constructor {h.name}")
  if d.abstract && (← atRuntime) then
    err s!"[K3] the constructor {h.name} of the abstract type {ty} at runtime, outside model code (an `implemented by` body, or a function taking or returning an unsized value)"
  let some (_, fields) := d.ctors[c]? | err s!"{ty} has no constructor {c}"
  if fields.length != as.length then err s!"{h.name} takes {fields.length} fields, given {as.length}"
  let np := d.params.length
  if !pts.isEmpty && pts.length != np then err s!"{h.name} takes {np} parameters, given {pts.length}"
  let (evs, etys) ← evalParams fuel' ty pts typed
  if typed && !pts.isEmpty then checkParams fuel' d ty evs etys
  let hint ← if pts.isEmpty then forceHint fuel' hint else pure hint
  let mut sol : Array (Option Value) := if !pts.isEmpty then evs.map some else match hint with
    | some (.tInd m ps) => if m == ty && ps.length == np then (ps.map some).toArray else Array.replicate np none
    | _ => Array.replicate np none
  -- D105: the inference at every position a field's type names, read only to say why a
  -- parameter that `sol` leaves unsolved is not inferred
  let mut solAll := sol
  let mut tys := #[]
  let mut ws0 : Array Value := #[]
  -- D64: a dependent field's hint is its type at the fields evaluated so far
  let dep := d.dependent c
  -- one mental model: a proof constructor's arguments are statement positions
  let stmtC ← ctorIsProof ty
  -- D82: an untyped run reads the fields' types to infer the parameters of a type its context
  -- reads; D88: and whenever the parameters are not written, so the value records them
  let want ← wanted
  let wantFields := typed || (pts.isEmpty && np > 0)
  for ((a, (_, FT)), i) in (as.zip fields).zipIdx do
    -- D124: the untyped run hands a field its type exactly where the typed check does (it used to
    -- hand it where the field needed its context, D89, whether or not typing handed it)
    let fh ← if ((np > 0 && (a matches .ctor .. | .prim "rewrite" _ | .prim "rewriteR" _)) || (a matches .val _)
        || (dep && d.fieldDependent c i)) && (typed || (← readsHint fuel' false false a))
      then fieldTypeAt fuel' d sol c i ws0.toList else pure none
    demand wantFields
    let (w, T) ← stmtArgIf fuel' stmtC a (eval fuel' typed a fh)
    -- D105: a parameter is inferred from the field's type only at the positions the model
    -- follows (`Decide.inferFrom`)
    if let some T := T then
      if sol.any (·.isNone) then
        sol := unifyParams np (← inferFrom fuel' FT) T sol
        solAll := unifyParams np FT T solAll
    tys := tys.push T
    pushTemp w T "evalCtor"
    ws0 := ws0.push w
  -- D115: the fields stay temporaries of this frame until the value is built
  let ws ← topTemps as.length
  let proof ← ctorIsProof ty
  if !typed then
    let ws ← popTemps as.length
    -- D82: its declared type, the inductive at its parameters, when they are written or follow
    -- from the fields' types or the hint
    let T := if want && sol.all (·.isSome) then some (Value.tInd ty (sol.toList.filterMap id)) else none
    -- D88: the value records the parameters it inferred, so that it is self-describing; where
    -- its fields do not determine them (a proof field, a phantom parameter, no fields) the
    -- context's declared type does (D89: the hint, as typing has it)
    let ps := if pts.isEmpty && sol.all (·.isSome) then sol.toList.filterMap id else evs.toList
    return (if proof then .proof else .ind ty c h ps ws.toList, T)
  let mut ps := #[]
  for ((s, (ph, _)), k) in (sol.toList.zip d.params).zipIdx do
    match s with
    | some p => noBorrowParam ty p; ps := ps.push p
    | none =>
      if (solAll[k]?.join).isSome then
        err s!"cannot infer the parameter {ph.name} of {h.name}: it stands in its fields' types only at positions of a universe above Type₀ (a type in Type₁, a value of one, a function into a universe), where a parameter is not inferred (D105): write it, {h.name}[…](…), or annotate, ({h.name}(…) : {ty}(…))"
      err s!"cannot infer the parameter {ph.name} of {h.name}: write it, {h.name}[…](…), or annotate, ({h.name}(…) : {ty}(…))"
  -- [T-Ctor], D64: each field against its type computed from the earlier fields' values
  for (T, (fname, FT)) in tys.toList.zip (← fieldTypesOf fuel' d ps.toList c ws.toList) do
    expectTy fuel' s!"field {fname} of {h.name}" T FT
  let ws ← popTemps as.length
  let v := if proof then Value.proof else .ind ty c h ps.toList ws.toList
  pure (v, some (.tInd ty ps.toList))
termination_by structural fuel

-- ### Calls: [Call], P5, [Call-type], [Close], [Rec]

/-- One mental model: does `fv` return a type or a proof (its class, D28/D35)? Its arguments are
then statement positions. -/
def stmtCallee (fuel : Nat) (fv : Value) (fT : Option Value) : M Bool := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← funType? fuel' fv fT with
  -- `T` need not be a Π-type here (`f : A` with `A : Type`), and `fnClass` of anything else is
  -- `0`. That is never a decision of an accepted run: `evalCall` passes the same callee to
  -- `callFn`, which rejects it ("not a function type") before reading a class or row. The
  -- order is load-bearing for `Stability.DecisionsCommute`, whose `fnClass` and `closeRow`
  -- fields speak of Π-type values only (test: `CallSort`, `Examples/Functions.lean`)
  | some T => pure ((← fnClass fuel' T) != 0)
  -- a proof is only ever called at a proposition (P5): its calls return proofs. Any other value
  -- with no readable Π-type is not callable, and `callFn` rejects the call
  | none => pure (fv == .proof)
termination_by structural fuel

def evalCall (fuel : Nat) (typed : Bool) (f : Term) (as : List Term) (head : Bool) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D80: what the call's declared result type says (η at `Unit`, R2), and which borrow
  -- arguments lend a place whose declared type reads as `Unit` ([Close]'s fill, R3), read off
  -- the call as written, before it runs. A sealed program's head call keeps the decision its
  -- call made when it closed off (no η: it returned this program, so it did not read `Unit`)
  let res ← if head then pure DeclInfo.other else withLive true (declOf fuel' false [] [] (.call f as head))
  let argDecls ← as.toArray.mapM fun a => withLive true (declOf fuel' false [] [] a)
  let fills := argDecls.map (· == .ref .unit)
  modify fun s => { s with headEval := true }
  -- D78 [Rec]: a call made through a function's binding of itself (or a capture of it) is
  -- a recursive call of that function, read from the head's syntax (`recFrameOf`)
  let recUid? ← callRecUid f
  -- D53 (e): a call does not consume the function it calls (read in place)
  if f matches .place _ then modify fun s => { s with inPlace := true }
  -- D82: the head's type is the call's declared Π-type (`piTy`), read whatever the call is
  let want ← wanted
  -- D130: read from the copy `evalAt` made for this evaluation (it consumed the flag)
  let defer := (← get).deferHere
  demand true
  let (fv, fT) ← eval fuel' typed f
  modify fun s => { s with inPlace := false }
  -- D104: the head and each argument are held at the type their evaluation returned
  pushTemp fv fT "evalCall"
  -- one mental model: a call that returns a type or a proof is a statement, and each of its
  -- arguments a statement position, run on its own private copy of the state
  let stmt ← stmtCallee fuel' fv fT
  let mut tys := #[]
  let mut ws0 := #[]
  let mut ender := #[]     -- the editor: which argument ended each argument's borrow
  for ((a, ad), i) in (as.zip argDecls.toList).zipIdx do
    -- v2.0: a constructor argument's parameters may come from the parameter's type
    -- D124: the untyped run hands it exactly where the typed check does (it used to hand it where
    -- the argument needed its context, D89, whether or not typing handed it)
    let hint ← if (a matches .ctor .. | .val _ | .prim "rewrite" _ | .prim "rewriteR" _ | .prim "hole" _)
        && (typed || (← readsHint fuel' false (ad matches .ref _) a))
      then argHint fuel' fv fT ws0 else pure none
    -- D82: a borrow argument's type is a cell's if the call closes off ([Close]); an argument is a
    -- borrow exactly when its declared type is (D48)
    demand (ad matches .ref _)
    let (w, T) ← stmtArgIf fuel' stmt a (eval fuel' typed a hint)
    pushTemp w T "evalCall"
    ws0 := ws0.push w
    ender ← noteEnders ender ws0
    tys := tys.push T
  -- D115: the head and the arguments stay in Ω, the last temporaries of this frame, until the
  -- callee's frame binds them (`callFn` reads them there)
  let (_, ws) ← callTemps (← topIdx) as.length
  atLoc (← enderLoc ender ws) <| callFn fuel' typed fT as.length tys head recUid? res fills want defer
termination_by structural fuel

/-- The type of the next parameter of `fv`, with the earlier ones bound to the arguments
evaluated so far (a hint for a constructor argument's parameters; `none` if unknown). -/
def argHint (fuel : Nat) (fv : Value) (fT : Option Value) (ws : Array Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let some (.tPi cs (.pi hs ds c) rd) ← funType? fuel' fv fT | return none
  let some d := ds[ws.size]? | return none
  privately do
    pushFrame
    pushCaps fuel' cs rd
    let (pds, _) ← paramDecls fuel' cs rd hs ds c
    for (((d', h), w), pd) in ((ds.zip hs).zip ws.toList).zip pds do
      let A ← evalType fuel' d'
      let pd' ← refineDecl pd
      takeArgBorrow w
      pushBind h (some A) (etaUnit pd w) pd'.isProof pd'
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
  | .clo cs (.fix _ hs ds c _ _) rd => pure (some (.tPi cs (.pi hs ds c) rd))
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

/-- [Call-type]: the result type is `B` evaluated at the call point (after the
arguments are evaluated) with each parameter bound to its argument's value (a borrow
argument moved into it). The other free variables of `B` were captured when the
Π-type was formed. Each argument is checked against its parameter's type. -/
def callType (fuel : Nat) (piTy : Value) (ws : Array Value) (tys : Array (Option Value)) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .tPi cs (.pi hs ds c) rd := piTy | err s!"not a function type: {piTy}"
  if ds.length != ws.size then err s!"arity: {ds.length} parameters, {ws.size} arguments"
  let pf ← paramFlags fuel' cs rd ds
  let argLocs := (← get).locs.callArgs     -- the editor: the arguments' ranges
  privately <| unlocated do     -- the callee's parameter types are not this point's code
    pushFrame
    pushCaps fuel' cs rd
    let (pds, _) ← paramDecls fuel' cs rd hs ds c
    for (((d, h), i), pd) in ((ds.zip hs).zipIdx).zip pds do
      let A ← evalType fuel' d
      noteLoc argLocs[i]?.join (.expected A)
      atLoc argLocs[i]?.join <| expectTy fuel' s!"argument {i + 1} ({h.name})" tys[i]! A
      takeArgBorrow ws[i]!
      pushBind h (some A) (etaUnit pd ws[i]!) (pf.getD i false) (← refineDecl pd)
    evalType fuel' c
termination_by structural fuel

/-- D82: [Call-type]'s type without its argument checks: the declared codomain of `piTy` at the
arguments, each parameter bound at its declared type. The machine's type of a call. -/
def declCallType (fuel : Nat) (piTy : Value) (ws : Array Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (cs, hs, ds, c, rd) ← callPi piTy ws.size
  let pf ← paramFlags fuel' cs rd ds
  privately <| unlocated do
    pushFrame
    pushCaps fuel' cs rd
    let (pds, _) ← paramDecls fuel' cs rd hs ds c
    for (((d, h), i), pd) in ((ds.zip hs).zipIdx).zip pds do
      let A ← evalType fuel' d
      takeArgBorrow ws[i]!
      pushBind h (some A) (etaUnit pd ws[i]!) (pf.getD i false) (← refineDecl pd)
    evalType fuel' c
termination_by structural fuel

/-- D124: a hint handed down unevaluated (`hintLater`, a called body's declared codomain at its
arguments) is evaluated where it is read: a constructor with its parameters not written, an
embedded value, `rewrite`. Any other hint is itself. -/
def forceHint (fuel : Nat) (hint : Option Value) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match hint with
  | some (.sealed (.prim "⋄hint" (.val P :: as))) =>
    some <$> declCallType fuel' P (as.filterMap fun | .val v => some v | _ => none).toArray
  | h => pure h
termination_by structural fuel

/-- D82: the declared types of the parameters `need` of the Π-type `piTy` at the arguments `ws`
(as passed), and of the earlier parameters their types mention, each evaluated in the frame of
the captures and the earlier parameters, where it was written; `none` for the others, which are
bound untyped and not read (a type reads only the variables it mentions). -/
def paramTypes (fuel : Nat) (piTy : Value) (ws : List Value) (need : List Nat) :
    M (Array (Option Value)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .tPi cs (.pi hs ds c) rd := piTy | err s!"not a function type: {piTy}"
  let n := ds.length
  -- the parameters to evaluate: `need`, closed under the earlier parameters each mentions
  let mut want := Array.replicate n false
  for i in need do if i < n then want := want.set! i true
  for i' in [0:n] do
    let i := n - 1 - i'
    if want[i]! then
      for j in (ds[i]!).freeVars do
        if j < i then want := want.set! (i - 1 - j) true
  if !want.any id then return Array.replicate n none
  let pf ← paramFlags fuel' cs rd ds
  let (pds, _) ← paramDecls fuel' cs rd hs ds c
  privately do
    pushFrame
    pushCaps fuel' cs rd
    let mut out := #[]
    for (((((h, w), p), pd), d), i) in ((((hs.zip ws).zip pf).zip pds).zip ds).zipIdx do
      let A ← if want[i]! then some <$> evalType fuel' d else pure none
      out := out.push A
      takeArgBorrow w
      pushBind h A (etaUnit pd w) p pd
    pure out
termination_by structural fuel

/-- D82: the stored type of the binding at `pos`, its declared type, evaluating a deferred
parameter type (`Binding.lazyTy`) when it is read. -/
def bindTy? (fuel : Nat) (pos : Pos) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if let some T ← tyAt pos then return some T
  let .bind f i := pos | return none
  let some (P, ws, j) := (← get).env[f]!.binds[i]!.lazyTy | return none
  let .tPi _ (.pi _ ds _) _ := P | err s!"not a function type: {P}"
  if j < ds.length then pure (← paramTypes fuel' P ws [j])[j]!
  else some <$> declCallType fuel' P ws.toArray
termination_by structural fuel

/-- P5: the borrow arguments of a call that is not run end unchanged. D115: the call's head and
its `n` arguments are the last temporaries of the top frame (`callTemps`), held with their types
(D104); each borrow argument ends where it is held, the others still in Ω, and then the call's
temporaries are taken off. -/
def endBorrowArgs (fuel : Nat) (n : Nat) (hd : Nat := 1) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f ← topIdx
  for i in [0:n] do
    if let .borrow l _ ← getAt (← callArgPos f n i hd) then endBorrow fuel' l
  dropTemps f (n + hd)
termination_by structural fuel

/-- [Call]: push a frame `[caps, self, x̄ ↦ w̄]`, run the body, pop the frame. `B` is the call's
type, as the call has it (D104: the body's result is held at it across the frame's pop). D115: the
head and the arguments `ws` are the last temporaries of the caller's frame until the frame binds
them, moved out of the temporaries (`takeCallTemps`) with nothing run in between. -/
def runBody (fuel : Nat) (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value)
    (B : Option Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .fix self hs ds c _ body := t | err "internal: not a fix"
  -- K2/K3: a model function's body never runs at runtime
  let model ← match fv with
    | .gfn n => do pure (← lookupGlobal n).model
    | _ => pure false
  if model then modify fun s => { s with modelDepth := s.modelDepth + 1 }
  let r ← onFail (runBodyCore fuel' fv cs t rd ws B self hs ds c body)
    (if model then modify fun s => { s with modelDepth := s.modelDepth - 1 } else pure ())
  if model then modify fun s => { s with modelDepth := s.modelDepth - 1 }
  pure r
termination_by structural fuel

def runBodyCore (fuel : Nat) (fv : Value) (cs : List Value) (t : Term) (rd : List (DeclInfo × Value)) (ws : Array Value)
    (B : Option Value) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (body : Term) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let d := (← get).depth
  if d ≥ 2000 then exhausted "call depth exceeded (a non-terminating recursion)"
  modify fun s => { s with depth := d + 1 }
  let pf ← paramFlags fuel' cs rd ds
  let (pds, cd) ← paramDecls fuel' cs rd hs ds c
  -- D82: every binding has its declared type, each parameter's evaluated in the frame of the
  -- captures and the earlier parameters, where it was written (no `self`), as at the generic call
  -- ([Def], [Call-type]). It is evaluated when it is read (`bindTy?`), except a borrow parameter's,
  -- which is evaluated now
  let piTy := Value.tPi cs (.pi hs ds c) rd
  let tys ← paramTypes fuel' piTy ws.toList ((pds.zipIdx.filter (·.1 matches .ref _)).map (·.2))
  let selfTy ← funType fuel' fv none
  let pds' ← pds.mapM refineDecl
  let f0 ← topIdx
  pushFrame
  pushCaps fuel' cs rd
  -- D115: the head and the arguments leave the caller's temporaries as the frame binds them
  let (fv, ws) ← takeCallTemps f0 ws.size
  -- `self` has its Π-type
  pushBind self (some selfTy) fv false (.pi cd)
  -- D80 (R2): a parameter whose declared type reads as `Unit` is `()`, at every call as at the
  -- generic one (`checkFix`)
  for ((((((h, w), p), pd), A), i), pd') in (((((hs.zip ws.toList).zip pf).zip pds).zip tys.toList).zipIdx).zip pds' do
    pushBind h A (etaUnit pd w) p pd'
    if A.isNone then
      modifyFrame (← topIdx) fun fr =>
        { fr with binds := fr.binds.modify (fr.binds.size - 1) ({ · with lazyTy := some (piTy, ws.toList, i) }) }
  -- D53: a body is code; a function whose calls are erased has an erased body (b)
  let erasedFn := (← fnClass fuel' (← funType fuel' fv none)) != 0
  -- D89: a tail constructor whose fields do not determine its parameters gets the declared
  -- codomain at the arguments, as typing's tail check gives it; D124: the body gets it always, as
  -- `checkFix` checks the body at its goal always
  -- D124: computed where it is read (`forceHint`), from the arguments as they are now: deferred
  -- unless an argument is a borrow, whose content [Access] may move before the read
  let hint ← if ← readsHint fuel' true false body then do
      if ws.all (fun w => !(w matches .borrow ..)) then pure (some (hintLater piTy ws))
      else some <$> declCallType fuel' piTy ws
    else pure none
  -- static ends: the body is in tail position, as `checkTail` checks it at the generic call
  modify fun s => { s with tailNext := true }
  let (v, _) ← withErasedIf erasedFn (eval fuel' false body hint)
  wholeReturned v
  -- D104: the result is held across the pop at the call's type, the declared type of the position
  -- it is headed for (the body's run is untyped and has none of its own)
  pushTempAt ((← topIdx) - 1) v B "runBodyCore"
  popFrame fuel'
  modify fun s => { s with depth := d }
  popTemp
termination_by structural fuel

/-- Static ends, rule 1: a call whose declared result is a borrow (its row `kind`, [Close]'s) lends
that borrow every place its borrow arguments `ws` lend, whether it runs or closes off. They are
marked for a label `g` reserved now (no borrow holds it yet, so the marks are inert while the call
runs: the callee cannot reach its caller's places, [Frame] F4), and `g` becomes the result's label
(D99, `lendResult`). A sealed block's text does the same at its cells (exp-block-text). -/
def lendArgs (fuel : Nat) (kind : Kind) (ws : Array Value) : M (Option Nat) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let lent := if kind == .ref then ws.toList.filterMap (fun | .borrow l _ => some l | _ => none) else []
  let g? ← if lent.isEmpty then pure none else some <$> freshLoan
  if let some g := g? then
    fire .Lend fun _ => s!"the result is lent every place its {lent.length} borrow argument(s) lend"
    for l in lent do lendEnv fuel' (.mark l g)
  pure g?
termination_by structural fuel

/-- D99: the result is the fresh borrow `g` (`lendArgs`), whether the body ran or the call closed
off. The borrow the body returned (a borrow argument, made before the call, or one made inside
it) or [Close]'s `k` is ended into `g`: its loans and marks become `g`'s, so after the call no label
made before it is the result's, on every path, as in the meaning of the call. D115: the result is
held as a temporary, at the call's type `T`, meanwhile, so the renaming reaches it as it reaches the
rest of Ω (`lendV`'s `into` renames the borrow `k` itself to `g`). -/
def lendResult (fuel : Nat) (g? : Option Nat) (r : Value) (T : Option Value) (site : String) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match g?, r with
  | some g, .borrow k _ => do
    if k == g then pure r else
    pushTemp r T site
    lendEnv fuel' (.into k g)
    popTemp
  | some g, _ => do
    pushTemp r T site
    lendEnv fuel' (.ended g [])
    popTemp
  | none, _ => pure r
termination_by structural fuel

/-- [Call] of the head and the `n` arguments held as the last temporaries of the top frame
(D115: `callTemps`; every caller pushes them, with the types `fT` and `tys` it has for them, and
they stay in Ω until the callee's frame binds them, a sealed program's text takes them ([Close]),
or they end unrun (P5)). -/
def callFn (fuel : Nat) (typed : Bool) (fT : Option Value) (n : Nat)
    (tys : Array (Option Value)) (head : Bool)
    (recUid? : Option Nat := none) (res : DeclInfo := .other) (fills : Array Bool := #[])
    (want : Bool := true) (defer : Bool := false) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f0 ← topIdx
  let (fv, ws) ← callTemps f0 n
  if let some i := ws.findIdx? (· == .bot) then
    err s!"[Call] argument {i + 1} is ⊥ at the call point (a later argument ended its borrow): an argument not of the parameter's type"
  -- A proof value is only ever called at a proposition: P5, not run.
  if fv == .proof then
    let B ← if typed then some <$> callType fuel' (← funType fuel' fv fT) ws tys
      else if want then some <$> declCallType fuel' (← funType fuel' fv fT) ws else pure none
    endBorrowArgs fuel' n
    setFlags (true, true)
    return (.proof, B)
  let piTy ← funType fuel' fv fT
  -- D82: the call's type is its declared codomain at the arguments; typing also checks the
  -- arguments against the parameter types ([Call-type]), the machine does not re-check them
  -- D82: a `let` bound to the call takes its type lazily, unless the call returns a borrow
  let later := !typed && want && defer && !(res matches .ref _)
  -- D134: the deferred path makes the eager path's test when it records (`callPi`)
  if later then discard (callPi piTy ws.size)
  let B ← if typed then some <$> callType fuel' piTy ws tys
    else if want && !later then some <$> declCallType fuel' piTy ws else pure none
  let setLater : M Unit := modify fun s => { s with callTyLater := if later then some (piTy, ws.toList) else none }
  setLater
  if typed then
    trace fun _ => s!"[Call-type] {fv}({", ".intercalate (ws.toList.map toString)}) : {B.getD .bot}"
    recCheck fv ws recUid?
  -- D54: the class and [Close] row are those of the function value's own declared Π-type,
  -- on every path (conversion only lets a value stand at a Π-type of its class and row, so
  -- this is also the static type's; a sealed function whose own type cannot be read here
  -- keeps the static one)
  let clsTy := (← funType? fuel' fv none).getD piTy
  -- [Close]'s row: v1.7 (D35) from the declared codomain. The order here is load-bearing for
  -- `Stability.DecisionsCommute`: the row and the class are read only after `callType` (typed
  -- runs) and `declKind` have rejected a callee whose type is not a Π-type, so every row and
  -- class a run that goes on decides is a Π-type's, the only case the conjecture states (an
  -- unknown `A : Type` refined to a Π-type would otherwise read a row and class the generic run
  -- never decided; test: `CallSort`, `Examples/Functions.lean`)
  let kind ← declKind fuel' clsTy
  -- D28, D35: the callee's class, read off its declared codomain
  let cls ← fnClass fuel' clsTy
  let kind := if kind == .prop then Kind.data else kind
  -- D53: an erased call cannot make whole a borrow it is passed (its effects vanish at runtime)
  if cls != 0 then wholeBorrowArgs ws "an erased call"
  if cls == 2 then
    endBorrowArgs fuel' n
    setFlags (true, true)
    return (.proof, B)
  -- static ends, rule 1 (`lendArgs`)
  let g? ← lendArgs fuel' kind ws
  -- D115: the marks map over Ω, the call's temporaries included: read them again
  let (fv, ws) ← callTemps f0 n
  -- a neutral head (v1.3), and a function whose check is under way (D135: its body is code the
  -- check has not finished with, `underCheck`), close off at once, except as [Seal]'s head call (D39)
  let closesOff ← match fv with
    | .abs _ | .sealed _ => pure true
    | _ => underCheck fv
  let r ← if closesOff then (if head then stuckNow else closeCall fuel' n kind res fills tys)
    else match fv with
    | .gfn _ | .clo _ _ _ =>
      let (cs, t, rd) ← fixOf fv
      -- [App-close]: a stuck body closes the call off; [App-head]: not a sealed program's head call
      catchStuck (runBody fuel' fv cs t rd ws B) fun on =>
        if head then throw (.stuck on) else closeCall fuel' n kind res fills tys
    | _ => err s!"call of {fv}, which is not a function"
  -- D99 (`lendResult`)
  let r ← lendResult fuel' g? r B "callFn"
  let r := if cls == 2 then Value.proof else r
  -- D80 (R2): the result of a call whose declared codomain reads as `Unit` is `()`, whether it
  -- ran or closed off, so the generic call and an instance normalise it alike
  setFlags (cls != 0, cls == 2)
  setLater      -- the body's calls made their own
  pure (etaUnit res r, B)
termination_by structural fuel

/-- [Close]: the call `f(w̄)` has a stuck body; the partial run has been discarded (the
state is back at the call point). `L := let cᵢ : Tᵢ = uᵢ`, `C := f(ā)` with `aᵢ = &cᵢ` for
the borrow arguments `wᵢ = borrow_ℓᵢ uᵢ` of type `&Tᵢ`; the result and the loans follow the
table. D82: each cell has its declared type, the lent place's (`tys`, the arguments' types),
so a re-run of the program is typed by declaration like any other run.

This and a stuck block (`closeBlock`) are the places a sealed program is made, both through
`closeWith`, which keeps closing off's obligations (`notes/closeoff-model.md`):
(C1) the text reconstructs the call exactly, the same function value, the other arguments as
values, each borrowed content in a fresh cell, the head call marked so a re-run cannot close
it again (C5); (C2) each output is its own projection, read by `peek`, which copies the
discarded run's cell; (C3) a returned borrow's final content is a parameter of every fill, the
inert loan `k`, filled when the borrow ends; (C8) the inputs are loan-free and whole
(asserted below). Every sealed program enters the state through `canonNeutral`, so a text
already generalised in this world is its `σ` (C6). D80: whether the result is `()` (`res`, the
call's declared result type) and which fills are (`fills`, the borrow arguments that lend a
place declared `Unit`) are read off the call as written (`evalCall`), never off a value. -/
def closeCall (fuel : Nat) (n : Nat) (kind : Kind) (res : DeclInfo := .other)
    (fills : Array Bool := #[]) (tys : Array (Option Value) := #[]) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (fv, _) ← callTemps (← topIdx) n
  closeWith fuel' n 1 s!"{fv}" (fun as => .call (.val fv) as true) kind res fills tys
termination_by structural fuel

/-- [Close] for a head `C` (exp-block-text): a call's, `f(ā)ʰ` (`closeCall`), or a stuck block's
text, the match over its cells (`closeBlock`). Its `n` arguments are the last temporaries of the
top frame, above `hd` head temporaries (a call holds its head, a block none). `L := let cᵢ = uᵢ` for
the borrow arguments, and `C` is given the arguments with `&cᵢ` for those, the values for the
rest; the result and the loans follow the table. -/
def closeWith (fuel : Nat) (n hd : Nat) (what : String) (mkC : List Term → Term) (kind : Kind)
    (res : DeclInfo) (fills : Array Bool) (tys : Array (Option Value)) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D115: the head and the arguments are the last temporaries of the top frame until the program's
  -- text takes them: each borrow argument as its loan is filled, the rest at the end
  let f0 ← topIdx
  let ws ← argTemps f0 n
  fire .Close fun _ => s!"{what}: {if kind == .ref then "a borrow result" else if res == .unit then "a declared `Unit` result, ()" else "a sealed result"}"
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
  let C (d : Nat) : Term := mkC ((List.range ws.size).map (argT d))
  let cellTerm (i : Nat) (u : Value) : Term := match tys[i]? with
    | some (some (.tRef T)) => .ascribe (.val u) (.val T)
    | _ => .val u
  let wrapL (body : Term) : Term :=
    (bs.zipIdx).foldr (fun ((i, _, u), j) acc => .letIn ⟨s!"c{j + 1}"⟩ (cellTerm i u) acc) body
  let cell (d j : Nat) : Term := .place (.var (d + m - 1 - j))
  -- D53: the final read of a sealed program (its `K`) is an observation: it copies, while
  -- the program before it runs with runtime semantics
  let peek (t : Term) : Term := .prim "peek" [t]
  match kind with
  | .ref =>
    let k ← freshLoan
    -- D137: no η here. A fill at a place declared `Unit` keeps the hole `k` like any other: `()`
    -- would leave `k` in no place, so writes through the returned borrow would be observed nowhere
    -- (`ClosingOff.UnitFill`, `QU`)
    for ((i, l, _), j) in bs.zipIdx do
      let fill := wrapL (.letIn ⟨"r"⟩ (C 0) (.seq (.assign (.deref (.var 0)) (.val (.loan k))) (peek (cell 1 j))))
      -- D115: the argument's borrow is consumed (its content is the program's cell `cⱼ`), as [End]
      -- takes a borrow before it fills its loan
      setAt (← callArgPos f0 n i hd) .bot
      substEnv fuel' (.loan l) (← canonNeutral (.sealed fill)) false
      -- static ends: `l` is consumed; the places it lent are `k`'s (marked by `callFn`, rule 1)
      lendEnv fuel' (.ended l [])
    dropTemps f0 (n + hd)
    pure (.borrow k (← canonNeutral (.sealed (wrapL (.letIn ⟨"r"⟩ (C 0) (peek (.place (.deref (.var 0)))))))))
  | _ =>
    for ((i, l, _), j) in bs.zipIdx do
      -- D80 (R3): the fill of a place whose declared type reads as `Unit` (read off the call's
      -- argument as written, `&c` with `c : Unit`) is `()`, η-normal: never because its content
      -- happens to be `()`, which an instance can know where the generic call does not
      let fill ← if fills.getD i false then pure .unit
        else canonNeutral (.sealed (wrapL (.seq (C 0) (peek (cell 0 j)))))
      -- D115: the argument's borrow is consumed (its content is the program's cell `cⱼ`)
      setAt (← callArgPos f0 n i hd) .bot
      substEnv fuel' (.loan l) fill false
      -- static ends: `l` is consumed, so the places it lent are free
      lendEnv fuel' (.ended l [])
    dropTemps f0 (n + hd)
    -- D80 (R2): the readback at a declared `Unit` is `()` (η-normal form); the call's effects
    -- are in the fills above
    if res == .unit then return .unit
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

def evalMatch (fuel : Nat) (typed : Bool) (p : Place) (z s : Term) (expected : Option Value := none)
    (tail : Bool := false) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D81 [Proj]: a scrutinee with a field step `q.i` is named by a match on `q` first
  if let some (q, i, rebuild) ← projIn fuel' p then
    let (q, n, arms) ← projMatch fuel' q i (fun f => .matchNat (rebuild f) z s)
    return ← evalMatchInd fuel' typed q n arms expected tail
  if typed then natScrutinee fuel' p
  accessPath fuel' p
  accessNeutralHead fuel' p
  let v ← matchContent p
  match v with
  -- D84 [Join]: what another arm moves is dropped at this arm's end
  | .zero => do let w ← wanted; joinEnds fuel' (.matchNat p z s) tail (do demand w; modify fun s => { s with tailNext := tail }; eval fuel' typed z (if typed then none else expected))     -- D82: an arm is the match's tail
  | .succ _ => do let w ← wanted; joinEnds fuel' (.matchNat p z s) tail (do demand w; modify fun s => { s with tailNext := tail }; eval fuel' typed s (if typed then none else expected))
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ => if typed then splitThenClose fuel' p z s σ expected else stuckOn v
  | .sealed _ | .loan _ =>
    if !typed then stuckOn v
    else
      -- D84: a sealed program this world already generalised (on another private copy, kept
      -- by D37) is its record's value, so both sides of an `Id` name its parts alike
      if let some r ← recordedNeutral v then
        substEnv fuel' v r true
        let expected ← expected.mapM (substV fuel' v r)
        return ← evalMatch fuel' typed p z s expected tail
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
  let σ ← freshAbsR fuel' T
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
  -- exp-block-text: a sealed block's type is recorded in its text
  | .block _ _ _ B _ => pure (some B)
  | .call (.val f) as true =>
    match f with
    | .gfn n => match (← lookupGlobal n).ty with
      | .tPi cs (.pi hs ds c) _ =>
        if c.freeVars.isEmpty then pure (some (← evalType fuel' c)) else
        let np := ds.length
        let ws : Array (Option Value) := (as.map fun | .val v => some v | _ => none).toArray
        unless cs.isEmpty && ws.size == np && c.freeVars.all (fun j => j < np && (ws[np - 1 - j]!).isSome) do
          return none
        privately do
          pushFrame
          -- D82: each known parameter at its declared type; an unknown one is `⊥`, which `c`
          -- does not read (the guard above)
          for ((h, w), (d, i)) in (hs.zip ws.toList).zip ds.zipIdx do
            let A ← if w.isSome && d.freeVars.all (fun j => j < i && (ws[i - 1 - j]!).isSome)
              then some <$> evalType fuel' d else pure none
            pushBind h A (w.getD .bot)
          some <$> evalType fuel' c
      | _ => pure none
    | _ => pure none
  | _ => pure none
termination_by structural fuel

/-- Re-normalise every sealed program in the state (after a generalised neutral has been
refined, sealed programs whose runs derive it may now make progress), at every position a
refinement reaches (`mapState`, with types; types re-normalise as types: erased, D53). -/
def renormAll (fuel : Nat) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  mapState (fun v => renormV fuel' v) true
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
  | .gloan l w => return .gloan l (← renormV fuel' w)
  | .ind ty c h ps fs => return .ind ty c h (← ps.mapM (renormV fuel')) (← fs.mapM (renormV fuel'))
  | .tEq A a b => mkEqM fuel' (← renormV fuel' A) (← renormV fuel' a) (← renormV fuel' b)
  | .tInd n as => return .tInd n (← as.mapM (renormV fuel'))
  | .tRef A => return .tRef (← renormV fuel' A)
  -- closures and Π-types too: their captures and embedded values (arrays-library: a goal
  -- `… ∧ Π(…). …` whose Π captured a sealed program stayed stale after a split)
  | .clo cs t rd =>
    let rd' ← rd.mapM fun (d, T) => do pure (d, ← renormV fuel' T)
    return .clo (← cs.mapM (renormV fuel')) (← renormT fuel' t) rd'
  | .tPi cs t rd =>
    let rd' ← rd.mapM fun (d, T) => do pure (d, ← renormV fuel' T)
    return .tPi (← cs.mapM (renormV fuel')) (← renormT fuel' t) rd'
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
  | .ref u => return .ref (← go u)
  | .cong a b => return .cong (← go a) (← go b)
  | .ascribe a b => return .ascribe (← go a) (← go b)
  | .eq a b c => return .eq (← go a) (← go b) (← go c)
  | .id a b c => return .id (← go a) (← go b) (← go c)
  | .prim n as => return .prim n (← as.mapM go)
  | .ctor ty c h ps as => return .ctor ty c h (← ps.mapM go) (← as.mapM go)
  | .tind n as => return .tind n (← as.mapM go)
  | .matchInd p ty as => return .matchInd p ty (← as.mapM fun (h, a) => do pure (h, ← go a))
  | .block cs rd pf B m =>
    let rd' ← rd.mapM fun (d, T) => do pure (d, ← renormV fuel' T)
    return .block (← cs.mapM fun (h, a) => do pure (h, ← go a)) rd' pf (← renormV fuel' B) (← go m)
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
    [(pure .zero, z), (do pure (.succ (.abs (← freshAbsR fuel' .tNat))), s)] expected
termination_by structural fuel

/-- The general form: one arm per constructor, each checked under the refinement its
builder produces (fresh abstract values for the fields), then close off (`closeBlock`, which
runs the arms). -/
def splitArmsThenClose (fuel : Nat) (mt : Term) (σ : Nat) (arms : List (M Value × Term))
    (expected : Option Value) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let blockArms := arms.map fun (mk, arm) => BlockArm.mk
    -- D91: the block's entry, before the arms, may have η-refined the scrutinee itself (its type
    -- has one constructor and an arm moves a field of it, `movedPlace`); its one arm is then
    -- checked at that refinement, recorded for this world (D68, D79), not at a fresh one
    (do let r ← match (← get).etaRefs.lookup σ with
          | some r => pure r
          | none => mk
        refine fuel' σ r; pure r)
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
    let d ← lookupInd n
    -- D107: not a type whose declaration is being checked
    if d.declaring then err (d.declaringMsg s!"a match on {← ppPlace p}")
    pure (d, ps)
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
    (expected : Option Value) (tail : Bool := false) : M (Value × Option Value) := do
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
    | some (_, a) => do demand (← wanted); return ← eval fuel' typed a
    | none => err s!"[Match] no arm for constructor {c}"
  -- D49 (2): a match on a proof of a non-subsingleton is erased (its checked arms are all
  -- proofs), so a run does not run it: its value is ⋆ (read from the declaration)
  if !typed && !large then
    setFlags (true, true)
    return (.proof, none)
  if let [(_, a)] := arms then
    let a ← if typed then bindDataFields fuel' p d ps 0 a else pure a
    demand (← wanted)
    -- static ends: its one arm is in tail position where the match is (`checkTail` checks it so)
    modify fun s => { s with tailNext := tail }
    -- D124: in tail position the untyped run hands the arm the hint, as `checkTail` hands it the goal
    let r ← eval fuel' typed a (if typed || !tail then none else expected)
    if needProof && !(← getFlags).2 then subErr
    return r
  if !typed then
    -- not reached by checked programs (a subsingleton has at most one constructor): an
    -- erased match is ⋆, otherwise no arm can be chosen and the match is stuck
    let pf ← inWorld (← enterWorld) do
      discard (eval fuel' false arms[0]!.2)
      pure (← getFlags).2
    if pf then setFlags (true, true); return (.proof, none)
    stuckNow
  let w ← enterWorld
  let mut tys := #[]
  let mut allProof := true
  for ((_, a0), c) in arms.zipIdx do
    let (T, pf) ← inWorld w do
      let a ← bindDataFields fuel' p d ps c a0
      let (_, T) ← eval fuel' true a
      let pf := (← getFlags).2
      let some T := T | err "internal: untyped arm"
      if let some E := expected then
        unless ← conv fuel' T E do err s!"an arm of the annotated match has type {T}, but the annotation is {E}"
      pure (T, pf)
    allProof := allProof && pf
    tys := tys.push T
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
    (expected : Option Value := none) (tail : Bool := false) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D81 [Proj]: a scrutinee with a field step `q.i` is named by a match on `q` first
  if let some (q, i, rebuild) ← projIn fuel' p then
    let (q, n, arms') ← projMatch fuel' q i (fun f => .matchInd (rebuild f) ty arms)
    return ← evalMatchInd fuel' typed q n arms' expected tail
  abstractMatchCheck p ty
  if ← byTypeMatch ty arms then return ← evalMatchByType fuel' typed p ty arms expected tail
  accessPath fuel' p
  accessNeutralHead fuel' p
  let v ← matchContent p
  match v with
  | .ind t c _ _ _ =>
    if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
    if typed then discard (scrutType fuel' p ty)
    match arms[c]? with
    | some (_, a) => do
      let w ← wanted
      let run := do demand w; modify fun s => { s with tailNext := tail }; eval fuel' typed a (if typed then none else expected)
      -- D93: a match on a type with one constructor has one arm and no other path to agree
      -- with: it never closes off in a typed run (an unknown is refined in place, below), so it
      -- has no entry (rule 2) and no join (D84), on every path
      if (← lookupInd ty).ctors.length == 1 then run
      else joinEnds fuel' (.matchInd p ty arms) tail run
    | none => err s!"[Match] no arm for constructor {c}"
  | .bot => err s!"[Match] on {← ppPlace p}, which was moved out"
  | .abs σ =>
    if !typed then stuckOn v
    else
      let (d, ps) ← scrutType fuel' p ty
      -- D93: an unknown of a type with one constructor is that constructor, so the match
      -- refines it in place and runs its one arm, as an instance does (above)
      if d.ctors.length == 1 then
        let r ← etaInPlace fuel' σ d ps
        fire .SplitOne fun _ => s!"σ{σ} := {r} (one constructor, in place)"
        let expected ← expected.mapM (substV fuel' (.abs σ) r)
        return ← evalMatchInd fuel' typed p ty arms expected tail
      splitArmsThenClose fuel' (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement fuel' d ps c, a)) expected
  | .sealed _ | .loan _ =>
    if !typed then stuckOn v
    else
      -- D84: a sealed program this world already generalised is its record's value (above)
      if let some r ← recordedNeutral v then
        substEnv fuel' v r true
        let expected ← expected.mapM (substV fuel' v r)
        return ← evalMatchInd fuel' typed p ty arms expected tail
      let (d, ps) ← scrutType fuel' p ty
      let σ ← generalizeNeutral fuel' p v
      let expected ← expected.mapM (substV fuel' v (.abs σ))
      -- D93: generalised, it is refined in place (above)
      if d.ctors.length == 1 then return ← evalMatchInd fuel' typed p ty arms expected tail
      splitArmsThenClose fuel' (.matchInd p ty arms) σ
        ((List.range d.ctors.length).zip (arms.map (·.2)) |>.map fun (c, a) => (ctorRefinement fuel' d ps c, a)) expected
  | _ => err s!"[Match] on {v}, which is not a value of {ty}"
termination_by structural fuel

/-- D68, D93: the unknown `σ` of the one-constructor declaration `d` (at the parameters `ps`) is
that constructor: it is refined in place, `σ := C(σ̄)`, an exhaustive [Split] with one arm. The
fields are the ones this world already named, if any (`etaRefs`: every private copy names them
alike, D68), else fresh ones, recorded for this world, since their types are read in it (D79). -/
def etaInPlace (fuel : Nat) (σ : Nat) (d : IndDecl) (ps : List Value) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let r ← match (← get).etaRefs.lookup σ with
    | some r => pure r
    | none => do
      let r ← ctorRefinement fuel' d ps 0
      modify fun s => { s with etaRefs := (σ, r) :: s.etaRefs }
      pure r
  refine fuel' σ r
  pure r
termination_by structural fuel

/-- D93: make the place `q` exist where a prefix of it holds an unknown of a one-constructor type,
or a sealed program of one (generalised first, D34, or replaced by this world's record of it):
each such prefix is refined in place (`etaInPlace`), as `movedPlace` refines one for a moved place.
A prefix that is missing for any other reason (an unknown of a type with several constructors) is
left as it is, and so is a fill over a live borrow, which generalising would lose (D90's `G1`):
`closeBlock` calls it after its entry has accessed the captures, which ends such a borrow first.
The field of a captured place is then a place, so the block's call takes it (`SB`). -/
def etaPlace (fuel : Nat) (q : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if (← content? q).isSome then return
  let some p := (match q with
    | .deref p | .proj _ p | .field _ p => some p
    | .var _ => none) | return
  etaPlace fuel' p
  if let some v ← content? p then
    if !(fillHoles (← get).env v).isEmpty then return
  let oneCtor (T : Value) : M (Option (IndDecl × List Value)) := do
    match T with
    | .tInd n ps => do
      let d ← lookupInd n
      pure (if d.ctors.length == 1 then some (d, ps) else none)
    | _ => pure none
  match ← content? p with
  | some n@(.sealed _) =>
    if let some T ← placeType? fuel' p then
      if (← oneCtor T).isSome then
        match ← recordedNeutral n with
        | some r => substEnv fuel' n r true
        | none => discard (generalizeNeutral fuel' p n)
  | _ => pure ()
  if let some (.abs σ) ← content? p then
    if let some (d, ps) ← oneCtor (← absType σ) then discard (etaInPlace fuel' σ d ps)
termination_by structural fuel

/-- D53: a place an arm moved out, as it exists in the closed-off (unrefined) state. The
arm's refinement may have exposed it (`q0.1` of an abstract pair): through a value of a
single-constructor type the abstract value is refined to that constructor, a total refinement
(as a split with one arm), a sealed one generalised first; a lent parent is reached by ending
its borrows. D94: what it returns is then
- the place itself, if it exists now, whatever made it exist (the join drops it, as an
  instance does);
- else the longest existing prefix, if that holds `⊥` or `⋆` (the drop does nothing, on every
  path), or a fill whose borrow the access did not end (below);
- and otherwise an error: the place does not exist, at an unknown or a stuck program of a type
  with several constructors, a constructor value without that field, or something that is not a
  borrow under `*`. The join's places are at the grain of the declared types (`Decide.jdGrain`),
  so such a place is ill-typed (an arm the run does not take is never checked): before D94 the
  prefix was dropped whole (fuzz-port M1's "longest prefix that exists"). -/
def movedPlace (fuel : Nat) (q : Place) : M Place := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if (← content? q).isSome then return q
  let parent : Place → Option Place
    | .deref p | .proj _ p | .field _ p => some p
    | .var _ => none
  let some p := parent q | return q
  let p ← movedPlace fuel' p
  -- D84, static ends: a place that holds a fill over a live borrow (its hole, a sealed program
  -- over the hole, or a known function of it, `fillHoles`), whether the call that lent it closed
  -- off or ran, is reached as the arm that moves out of it reaches it: [Access] ends the borrow
  -- (for a sealed program, as [Match] does, D29), which gives the place its content, so its
  -- fields are named on every path. Generalising a sealed program over a live hole would lose
  -- the hole (census, G1)
  if !(fillHoles (← get).env (← content p)).isEmpty then
    accessPath fuel' p; accessInside fuel' p
    -- kept as it is (D94): a fill whose borrow the access did not end is not generalised, which
    -- would lose its hole (census, G1), but dropped whole, the conservative direction. The
    -- access ends every borrow lent at `p`, so no run is known to take this exit
    if !(fillHoles (← get).env (← content p)).isEmpty then return p
    return ← movedPlace fuel' q
  match ← content p with
  | .abs σ =>
    match ← absType σ with
    | .tInd n ps =>
      let d ← lookupInd n
      if d.ctors.length == 1 then
        -- D68: the same fields in every private copy (a statement's sides each move out of `σ`);
        -- the record is this world's, since the fields' types are read here (`exitWorld`)
        discard (etaInPlace fuel' σ d ps)
        return ← movedPlace fuel' q
    | _ => pure ()
  | n@(.sealed _) =>
    -- D84: a sealed program of a type with one constructor is generalised (D34) and then
    -- η-refined, so its fields are named here as at an instance, where it is that constructor
    -- (the grain is the declared type's, `Decide.jdGrain`)
    if let some (.tInd tn _) ← placeType? fuel' p then
      if (← lookupInd tn).ctors.length == 1 then
        match ← recordedNeutral n with
        | some r => substEnv fuel' n r true
        | none => discard (generalizeNeutral fuel' p n)
        return ← movedPlace fuel' q
  | _ => pure ()
  -- D94: the place exists now (its parent was reached through a lent prefix): it is what is dropped
  if (← content? q).isSome then return q
  match ← content p with
  | .bot | .proof => pure p     -- the drop does nothing, as on every path
  | v =>
    let why := match v with
      | .abs _ => "an unknown of a type with several constructors"
      | .sealed _ => "a stuck program of a type with several constructors"
      | .ind .. => match q with
        | .deref _ => "a constructor value, which is not a borrow"
        | _ => "a constructor value without that field"
      | _ => match q with
        | .deref _ => "a value that is not a borrow"
        | _ => "a value without that field"
    err s!"[Join] an arm of the match moves {← ppPlace q}, which does not exist: {← ppPlace p} holds {why} ({v})"
termination_by structural fuel

/-- D84 [Join]: the places a match leaves moved, read from its syntax and declared types
(`Decide.jdMoves`), never from a run: the lattice join of its arms' end states, at the grain of
the declared types. Returns the places moved after it (the direct run's drops) and the ones of
them not moved before it (a stuck block's by-move captures, K1). -/
def staticJoin (fuel : Nat) (mt : Term) : M (List Place × List Place) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let f ← topIdx
  let binds := (← get).env[f]!.binds
  let nb := binds.size
  let entry := (List.range nb).flatMap fun o => botPlaces binds[nb - 1 - o]!.val (.var o)
  let u ← withLive true (jdMoves fuel' [] [] mt entry)
  let net := u.filter fun q => !entry.any (jdCovers · q)
  pure (u, net)

/-- D84: what an arm's log may say a static join's place moved: the place, and, for a move
through a borrow a local variable of this frame holds, the lender's part (`logEffect` records
both, `throughLocalBorrow`), which the move reaches through the borrow. -/
def joinLogged (st : List Place) : M (List Place) := do
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
  let mut out := st
  for q in st do
    if let .bind f' i ← varPos q.root then
      if let some (j, ss) ← throughLocalBorrow f' i q then
        out := jdAdd out (ss.foldl stepPlace (.var (nb - 1 - j)))
  pure out

/-- D84 [Join]: run an arm of a match on a known constructor, then drop what the join says is
moved and the arm left whole (`dropAtJoin`), the arm's result held as a temporary meanwhile. Its
flags are the arm's. -/
def joinDrop (fuel : Nat) (mt : Term) (run : M (Value × Option Value)) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (drops, _) ← staticJoin fuel' mt
  let (v, T) ← run
  if drops.isEmpty then return (v, T)
  let fl ← getFlags
  pushTemp v T "joinDrop"
  for q in drops do dropAtJoin fuel' (← movedPlace fuel' q)
  let v ← popTemp
  setFlags fl
  pure (v, T)
termination_by structural fuel

/-- D84 [Join] in tail position: the continuation of the arm drops what the join says first. It
ends a known constructor's arm and, since D119, each world's arm of a split, so the generic
call's end states are an instance's. -/
def joinCont (fuel : Nat) (mt : Term) (k : Value → Value → M Unit) : M (Value → Value → M Unit) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (drops, _) ← staticJoin fuel' mt
  if drops.isEmpty then return k
  pure fun r R => do
    let fl ← getFlags
    pushTemp r (some R) "joinCont"
    for q in drops do dropAtJoin fuel' (← movedPlace fuel' q)
    let r ← popTemp
    setFlags fl
    k r R
termination_by structural fuel

/-- Static ends, rule 2: a match not in tail position, run on a known constructor, ends and lends
as the stuck block it closes off as on an unknown one (`closeBlock`), so that which borrows are
live after it does not depend on which arm a run takes. At its entry, the places that block would
capture (`blockCaptures`, K1) are accessed as the block's arguments are, in its order, ending their
borrowers (`blockEntry`). If its declared type is a borrow, its result is lent what the block's
result would be, by [Close] and rule 1: the places it would take by `&`, and those the borrow
variables it would take by move lend. Then the arm runs and the join drops (D84, `joinDrop`). A
match in tail position is split at the generic call, never closed off, and runs as before. -/
def joinEnds (fuel : Nat) (mt : Term) (tail : Bool) (run : M (Value × Option Value)) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if tail then return ← joinDrop fuel' mt run
  let caps ← blockEntry fuel' mt
  unless (← withLive true (declOf fuel' false [] [] mt)) matches .ref _ do
    return ← joinDrop fuel' mt run
  -- the borrow variables the block would take by move: the places they lend are the result's,
  -- marked for a label reserved now (inert while the arm runs, as in a call: rule 1)
  let g ← freshLoan
  for (q, mode) in caps do
    if mode == 2 then
      if let some (.borrow j _) ← content? q then lendEnv fuel' (.mark j g)
  let (v, T) ← joinDrop fuel' mt run
  -- D115: the result is held in Ω, a temporary at its type, while the join lends and the marks
  -- for `g` are handed on
  pushTemp v T "joinEnds"
  match v with
  | .borrow k _ =>
    -- the places the block would take by `&`
    for (q, mode) in caps do
      if mode == 1 then
        if let some w ← content? q then setPlace q (lentTo [k] w)
    lendEnv fuel' (.ended g [k])
  | _ => lendEnv fuel' (.ended g [])
  pure (← popTemp, T)
termination_by structural fuel

/-- Static ends, rule 2: the entry of a match (or of `J`'s transported term) that a stuck block
would close off: the block's captures, accessed in `closeBlock`'s order (oldest binding first), as
its arguments are evaluated ([Access]: the borrowers of each place end). Returns the captures. -/
def blockEntry (fuel : Nat) (mt : Term) : M (Array (Place × Nat)) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let (_, st) ← staticJoin fuel' mt
  let (caps, _, _) ← blockCaptures fuel' mt st
  let capsS := caps.qsort fun (a, _) (b, _) => a.root > b.root || (a.root == b.root && (a.steps.2.length < b.steps.2.length))
  entryAccess fuel' capsS
  pure capsS
termination_by structural fuel

/-- Static ends: the entry of a match a stuck block would close off, and of the block itself
(`closeBlock`, before it takes its arguments): every capture is accessed, in order, before any
is taken, so the arms see the same state whether they run in the block or directly. (Taking a
read-only capture through a borrow before a later capture's access ended that borrow let the
block's arm read a copy the direct run's arm could not: `EK`, probes/static-ends/Snapshot.) -/
def entryAccess (fuel : Nat) (capsS : Array (Place × Nat)) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  for (q, mode) in capsS do
    fire .Entry fun _ => s!"a place a stuck block would capture"
    accessPath fuel' q
    if (← content? q).isSome then accessInside fuel' q
    -- D112: a capture by `&` invalidates as its borrow does ([Open]), on every path: the block's
    -- borrow of the place does when the match closes off, so the entry does when it runs directly
    if mode == 1 then openWrite fuel' q
termination_by structural fuel

/-- D84 [Join]: drop `q` as a stuck block's by-move argument takes it (`readPlace`): a borrow is
ended, a copy stays, a place already moved or not there stays, a part of a proof stays, anything
else is moved out, its borrowers ended first ([Access]).

D102: a place's own `⋆` is decided like any value, by the copy decision (since D100 every proof
is a copy, so it stays); only a place under a `⋆` (a part of a proof) is skipped by its
position. So the drop's "do nothing" is decided by the shared copy decision and by whether the
place exists, never by the value it holds. -/
def dropAtJoin (fuel : Nat) (q : Place) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match ← content? q with
  | none | some .bot => pure ()
  | some (.borrow l _) => fire .Join fun _ => s!"a borrow ended"; logEffect q "moves"; endBorrow fuel' l
  | some v =>
    if v == .proof && (← underProof q) then return
    if ← copyRead fuel' q then return
    -- [Drop] (D65 amended): a place dies while a value in flight borrows it, here the arm's
    -- result, which the match is about to return
    for l in liveLoansIn (← get).env v do
      if let some (.temp _ _) := findBorrow (← get).env l then
        err s!"[Join] {← ppPlace q} is moved by another arm of the match, so it is dropped at the end of this one, while the arm's result borrows it"
    let qs ← ppPlace q
    fire .Join fun _ => s!"{qs} dropped"
    accessPath fuel' q; accessInside fuel' q
    logEffect q "moves"
    setPlace q .bot
termination_by structural fuel

/-- K1 (`notes/erasure-model.md`): a stuck block's captures over-approximate every arm. For every
outer place the match uses, the block's mode is at least each arm's effect on it, in the order
copy (read in place, 0) ⊑ `&` (borrowed or assigned, 1) ⊑ move (2), and the captures are the
maximal places used. The clauses, in the order computed:
- (a) Moved places: D84, the match's join (`staticJoin`, `Decide.jdMoves`), read from syntax and
  declared types and at their grain, which the direct run drops too: a place an arm moves out,
  net of the arm's own refills, and every variable a closure or Π-type in any arm captures
  unless it is a copy, whether or not the run took that arm (D68). The arms' logs (`armMoves`)
  are an assertion in `closeBlock`. Each is re-rooted where it lives (`movedPlace`).
- (b) Modes by use: a borrow variable read or assigned whole is moved (its borrow ends with
  the block's frame); a variable some arm moves whole is moved; a borrow or an assignment is
  `&`; any other read is a copy.
- (c) Maximal places: the used places with no used strict prefix, each at the largest mode
  used under it.
- (d) A place an arm moves whole that is a strict prefix of captures is captured whole, by move.
- (e) A capture some arm moves out whole is moved, whatever its uses.
- (f) A proof is never taken by `&` (D66): its value is ⋆, so a write through a matched proof's
  pattern variable is local to the block's copy.
- (g) Granularity: a capture part of which an arm moves out is split into its fields, each
  captured by its own mode (`q.1` moved while `q.0` is lent), and the block's matches on the
  split place take the arm of its constructor; a place used whole other than as a scrutinee is
  moved whole instead.
Over-approximating is safe (K2): a stricter generic call only removes options from the code
after the block. Each clause began as a fuzz-port finding (14942, Q, M2, R8, shape (a), N3;
the comments below name them); a new one should be stated here as a clause of K1 first.
Returns the captures with their modes, the split places with each one's constructor, and the
moved places. -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 13): captures read a split capture's constructor, type-directed or surviving refinement; the moved places and their grain (D84, `staticJoin`) and copy-ness (D80, `copyRead`) are read from syntax and declared types.
def blockCaptures (fuel : Nat) (mt : Term) (armMovedAll : List Place) :
    M (Array (Place × Nat) × List (Place × Option Nat) × List Place) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- K1(a), moved places. D68: a closure or Π-type in an arm captures by move what it mentions (unless a copy), in a
  -- statement too, whether or not the run took that arm: the block takes the place by move on
  -- every path (fuzz case 14942: the abstract run's inner block moved it, the ground run's did
  -- not, and only the ground run found the closure capturing a borrowed place)
  let moved ← do
    let mut mv := armMovedAll
    for (o, p) in mt.fnOccs 0 do
      let q := p.mapRoot fun _ => .var o
      -- D80: a place whose declared type does not read as a copy type: the block moves it
      unless ← copyRead fuel' q do
        unless mv.any (placeEq · q) do mv := mv ++ [q]
    pure mv
  let moved ← moved.foldlM (fun acc q => do
      let q' ← movedPlace fuel' q
      pure (if acc.contains q' then acc else acc ++ [q'])) []
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
  -- K1(b), modes by use: the free places used, re-rooted at the frame index, with their capture mode
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
  -- K1(c), maximal places: places with no strict prefix among the used places
  let mut caps : Array (Place × Nat) := #[]
  for (q, _) in uses do
    let hasPrefix := uses.any fun (q', _) => placePrefix q' q && !(placeEq q' q)
    if !hasPrefix && !(caps.any fun (c, _) => placeEq c q) then
      let mode := (uses.filter fun (p, _) => placePrefix q p).foldl (fun m (_, k) => max m k) 0
      caps := caps.push (q, mode)
  -- K1(d). D53 (fuzz-port Q): a place some arm moved out whole that is a strict prefix of captures
  -- (a closure in an arm capturing `q0` for its `q0.1`) is moved in whole, covering them
  for m in moved do
    if caps.any (fun (c, _) => placePrefix m c && !placeEq m c) then
      caps := (caps.filter fun (c, _) => !placePrefix m c).push (m, 2)
  -- K1(e). D53 (fuzz-port M2): a capture that some arm moves out whole is moved in, whatever it is
  -- (`*x0`, `n1.1`), as the direct path moves it
  caps := caps.map fun (q, k) => if moved.any (placeEq · q) then (q, 2) else (q, k)
  -- K1(f). A proof is never taken by `&` (D66: its type is a proposition, not in Type₀): its value is `⋆`, so an
  -- arm's write through a pattern variable of a matched proof (a field, a fresh value by
  -- D49 (3), in a proof position by D45) is local to the block's own copy (R8, fuzz-port)
  caps ← caps.mapM fun (q, k) => do
    if k != 1 then return (q, k)
    let isProof ← match ← placeType? fuel' q with
      | some T => isPropV fuel' T
      | none => pure false
    pure (if isProof then (q, 0) else (q, k))
  -- K1(g), granularity. D53 (fuzz-port shape (a), N3): the block's captures mirror the direct path's effects,
  -- per sub-place. A capture part of which some arm moves out is split into its fields,
  -- each captured by its own mode (moved, `&`, or read in place), so that `q1.1` can be
  -- moved while `q1.2` is lent; the block's matches on the split place take the arm of its
  -- constructor. A place used whole otherwise than as a scrutinee is moved in whole.
  let mut split : List (Place × Option Nat) := []
  let mut todo := caps.toList
  let mut out : Array (Place × Nat) := #[]
  -- D109: a loop over the fuel, not a `while` (which Lean builds on a `partial` function): each
  -- round takes one place off `todo`, which ends when every split place's fields are taken, and
  -- running out of fuel first is "I don't know" (`exhausted`), never caught and never deciding
  for _ in [0:fuel'] do
    if todo.isEmpty then break
    let (q, k) := todo.head!
    todo := todo.tail!
    let inner := moved.filter fun m => placePrefix q m && !(placeEq m q)
    if k == 2 || inner.isEmpty then out := out.push (q, k); continue
    if wholeUses.any (fun (p, pk) => placeEq p q && pk != .scrut) then out := out.push (q, 2); continue
    let children : Option (Option Nat × List Place) ← match (← content q).unlent with
      | .ind t c _ _ fs => do
        let d ← lookupInd t
        let names := (d.ctors[c]?.map (·.2.map (·.1))).getD []
        pure (some (some c, fs.zipIdx.map fun (_, i) => Place.field ⟨t, c, i, names.getD i s!"f{i}"⟩ q))
      | .succ _ => pure (some (none, [Place.proj 0 q]))
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
  unless todo.isEmpty do exhausted "out of fuel"
  pure (out, split, moved)
termination_by structural fuel

/-- [Block], the one place a stuck block is formed (D76). A stuck match ([Split]), a `J` whose
endpoints are not convertible ([T-J-stuck]) and a zero-arm match outside a proof position are
closed off here (exp-block-text): its sealed text binds what it captured, each in a cell, and
is then the match itself over those cells, marked as the program's head (`.block`); it is not a
function, so nothing calls it (`runBlock` re-runs its text). Its captures are
computed first, from syntax and declared types, and its entry accesses them all (D91); then the
block runs its arms itself (`BlockArm`): each from the unrefined state after the entry, the state
a direct run's arm starts from, under its own setup, and each is checked to its return by
`bodyReturns`, the check every function body's return goes through. So a block
cannot be formed without its arms having been checked whole where its borrows end: the
producer obligation for the sealed programs a block leaves, of which D72 (a match's arms) and
D75 (a `J`'s transported term) were two instances found missing.

The places are captured (`blockCaptures`, K1) as Rust infers closure captures, on maximal place prefixes: a place
some arm moves out of is moved in; otherwise a place written or borrowed (under `&_` or left of
`:=`) in some arm is passed as `&`; otherwise a place read is copied. A borrow variable read as a
whole is a move (reading a borrow moves it); assigning a borrow variable as a whole moves it too
(passing `&x` would be `&&T`). The block's type is `B?`, or else its arms' common type. -/
-- Two paths, value-dependent by design (notes/two-paths-census.md, site 13): captures read a split capture's constructor, type-directed or surviving refinement; the moved places and their grain (D84, `staticJoin`) and copy-ness (D80, `copyRead`) are read from syntax and declared types.
def closeBlock (fuel : Nat) (mt : Term) (arms : List BlockArm) (B? : Option Value) :
    M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- K1: the block takes each outer place by the largest effect any arm has on it (`blockCaptures`);
  -- D84: the places it moves are the static join's, which the direct run drops; what the arms'
  -- runs moved is kept as an assertion that the two agree (below). D91: the captures are read
  -- from syntax and declared types, not from the arms' runs, so they are computed first, and the
  -- block's entry accesses them all ([Entry], `entryAccess`, D90) before any arm is checked: each
  -- arm is checked from the state a direct run's arm starts from, so the generic call and every
  -- instance agree on which borrows are live inside the arms too, with no exception
  let (_, st) ← staticJoin fuel' mt
  let (caps, split, moved) ← blockCaptures fuel' mt st
  -- order the captures by frame position (oldest binding first), then by path
  let capsS := caps.qsort fun (a, _) (b, _) => a.root > b.root || (a.root == b.root && (a.steps.2.length < b.steps.2.length))
  entryAccess fuel' capsS
  -- D93: a captured field of an unknown of a one-constructor type is a place once the unknown is
  -- refined in place, here, after the entry (which has ended any borrow over a fill on its path)
  -- and before the arms, in this world, as a moved place is (`movedPlace`); the block's call then
  -- takes it (the internal error `SB` reached before)
  for (q, _) in capsS do etaPlace fuel' q
  -- each arm runs in its own world (`enterWorld`/`inWorld`, split-model's (X)): a fact an arm
  -- learns is never visible in a sibling arm or after the block
  let w ← enterWorld
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
    let (av, T, pf, armMoved, armEnd) ← inWorld w do
      let r ← arm.setup
      let ls := (← get).placeLog.size
      let (av, T) ← arm.body r
      let pf := (← getFlags).2
      -- the arm's effect on the places it captures, read from its log of moves and
      -- assignments (D53: by place, at the granularity of the move, `q1.1`; an inner block's
      -- moves are its arguments', so they compose; fuzz-port M1, N1)
      let armMoved ← armMoves ((← get).placeLog.extract ls (← get).placeLog.size) f0 n0
      -- the arm's result is held as a temporary there, so that a borrow it returns into a
      -- lent place is still in Ω when that place is checked
      pushTemp av (some T) "closeBlock"
      pure (av, T, pf, armMoved, ← get)
    allProof := allProof && pf
    for q in armMoved do
      unless armMovedAll.any (placeEq · q) do armMovedAll := armMovedAll ++ [q]
    ends := ends.push (armEnd, av, T)
    tys := tys.push T
  let B ← match B? with
    | some E => pure E
    | none =>
      let some T0 := tys[0]? | err "internal: a match with no arms"
      for T in tys do
        unless ← conv fuel' T T0 do
          err s!"the arms of a non-tail match have different types ({T0} and {T}); annotate it (let x : T = match …)"
      pure T0
  -- D84: what the arms' runs moved agrees with the static join (an assertion)
  let logged ← joinLogged st
  for q in armMovedAll do
    unless logged.any (jdCovers · q) do
      err s!"INTERNAL [D84] an arm of a stuck match moves {← ppPlace q}, which the static join misses (please report)"
  let f ← topIdx
  let nb := (← get).env[f]!.binds.size
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
  -- [Return] at each arm's end (D76): each arm ends where the block's text ends (its cells are
  -- dropped there), and `bodyReturns` checks there what every function body's return is checked
  -- for. A place the block takes by borrow is reached through a borrow of its cell, which ends
  -- there; a borrow variable it moves in whole is dropped with its cell there too. So each such place must be of its type again in the state the arm ends in, and
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
      -- D87: a place the block takes by move is its by-value parameter, which dies where the
      -- arm returns, so the arm's result (held as a temporary) may not borrow it: D65's
      -- in-flight check at a function's return, and what [Join] checks when the match runs
      -- directly (`dropAtJoin`), with the same message, so both paths reject alike
      for (q, mode) in capsS do
        if mode == 2 then
          match ← content? q with
          | none | some .bot | some .proof | some (.borrow _ _) => pure ()
          | some v =>
            unless ← copyRead fuel' q do
              for l in liveLoansIn (← get).env v do
                if let some (.temp _ _) := findBorrow (← get).env l then
                  err s!"[Join] {← ppPlace q} is moved by another arm of the match, so it is dropped at the end of this one, while the arm's result borrows it"
      bodyReturns fuel' "a stuck match's arm returns it" av T lent "lent to a stuck match, whose arm returns with it")
      (set cur)
    set cur
  -- exp-block-text: a function whose check is under way (on the [Rec] stack) that the match
  -- names (only as the head of a call, fix L1) is named by its global in the text, never held as a
  -- cell (the checker's rule; D139's first part): K1 still takes its binding, so the state after
  -- the block is the direct run's, but the text does not keep it
  let recs := (← get).recStack
  let env0 := (← get).env
  let selfFn (q : Place) : Option Value := match q with
    | .var o =>
      let b := env0[f]!.binds[nb - 1 - o]!
      (recs.find? fun ctx => recFrameOf ctx b.val b.recUid).map (·.fn)
    | _ => none
  let mut hints := #[]
  let mut pflags := #[]
  let mut rd := #[]
  let mut fills := #[]
  let mut kept : Array (Place × Nat) := #[]
  let mut selfs : List (Nat × Value) := []
  -- every capture's argument, its domain, whether it takes it by `&`, and whether the text keeps it
  let mut takes : Array (Term × Value × Bool × Bool) := #[]
  for (q, mode) in capsS do
    let T ← placeType fuel' q
    -- D80: each cell is declared as the place it takes (its type `T` is for typing its value):
    -- the block's run reads its cells as the direct path reads the places, copy or not, whatever
    -- a refinement makes of `T`
    let dq ← withLive true (placeDecl fuel' [] q)
    repackAt fuel' q T "captured whole by a stuck match"
    -- a captured proof variable stays a proof in the block: its cell is a proof (v1.7: the same
    -- flag on the direct and the block path)
    let env := (← get).env
    let pflag ← match q with
      | .var o => pure (mode != 1 && env[f]!.binds[nb - 1 - o]!.proof)
      | .field g _ => do pure (mode != 1 && (← fieldIsProof g))   -- v2.0: a proof field (declared)
      | _ => pure false
    let (dom, arg) ← match mode with
      | 2 => pure (T, Term.place q)
      | 1 => do
        -- D66: the block borrows the place, so its type must be known to be in Type₀ (a stuck
        -- type `⌈T(σ)⌉` by its head's declared codomain: reviewer-6's A12)
        if !(← isBorrowable fuel' T) then
          err s!"[D66] a stuck match would borrow {← ppPlace q}, whose type {T} is not known to be in Type₀"
        pure (Value.tRef T, Term.borrow q)
      -- D53: a place the block only reads is read in place, not consumed
      | _ => pure (T, Term.prim "inplace" [Term.place q])
    match selfFn q, q with
    | some fn, .var o =>
      selfs := (o, fn) :: selfs
      takes := takes.push (arg, dom, mode == 1, false)
    | _, _ =>
      rd := rd.push (if mode == 1 then (DeclInfo.ref dq, Value.tRef T) else (dq, T))
      pflags := pflags.push pflag
      hints := hints.push (Hint.mk ((← ppPlace q).replace "*" "" |>.replace "(" "" |>.replace ")" "" |>.replace "." "_"))
      -- D80 (R3): a fill of a place declared `Unit` taken by `&` is `()`, read off the place
      fills := fills.push (mode == 1 && dq == .unit)
      kept := kept.push (q, mode)
      takes := takes.push (arg, dom, mode == 1, true)
  let capsL := kept.toList
  let n := capsL.length
  let mt := if split.isEmpty then mt else mt.selectArms (fun p => (split.find? (placeEq ·.1 p)).map (·.2)) 0
  -- the match over the cells: a kept capture's place is its cell (through `*` if taken by `&`), a
  -- function under check its global
  let mtG := selfs.foldl (fun t (o, fn) => t.inlineReads o (.val fn) 0) mt
  let body := mtG.mapFreePlace (fun c p =>
    match capsL.zipIdx.find? fun ((q, _), _) => placePrefix q p with
    | some ((q, mode), k) =>
      let cell := Place.var (c + n - 1 - k)
      let base := if mode == 1 then Place.deref cell else cell
      let (_, qs) := q.steps
      let (_, ps) := p.steps
      (ps.drop qs.length).foldl (fun acc st => match st with
        | .deref => .deref acc | .proj i => .proj i acc
        | .field g => .field g acc) base
    | none => p) 0
  let text (as : List Term) : Term := .block (hints.toList.zip as) rd.toList pflags.toList B body
  trace fun _ => s!"[Stuck block] {Value.sealed (text (takes.toList.filterMap fun (a, _, _, k) => if k then some a else none))}"
  -- v1.7 (D35): the block is erased exactly when its match would be, i.e. at every
  -- instance: when every arm is a proof (finding P2: not read off the computed type B).
  -- D80: its result is `()` exactly when the match's declared type reads as `Unit` (every arm's
  -- does), as the direct path's match is then `()` by its arms; never by `B`, which is computed
  let res ← withLive true (declOf fuel' false [] [] mt)
  -- static ends, rule 2: a direct run lends its result as this block does exactly when the
  -- match's declared type reads as a borrow (`joinEnds`); the block's [Close] row is read from
  -- `B` (`kindOf`). `&` is never produced by computation (D48), so the two agree
  let kind ← kindOf fuel' B
  unless (res matches .ref _) == (kind == .ref) do
    err s!"INTERNAL [static ends] the match's declared type and its type {B} disagree on whether it is a borrow (please report)"
  let kind := if kind == .prop then Kind.data else kind
  -- the block's type is `B`; no type is computed for what it takes (D82), nor deferred (D130)
  modify fun s => { s with wantHere := false, deferHere := false }
  -- [Block] takes its captures as a call takes its arguments: each evaluated in order into a
  -- temporary of this frame, held at its domain (D104, D115), a proof block's as statements (an
  -- erased call's are, `stmtArgIf`). A function under check's binding is taken as K1 says and not
  -- kept (its value is the global the text names)
  let f1 ← topIdx
  let mut argTys : Array (Option Value) := #[]
  for (a, dom, byRef, keep) in takes do
    demand byRef
    let (w, T) ← stmtArgIf fuel' allProof a (eval fuel' false a)
    if keep then
      pushTemp w (T <|> some dom) "closeBlock"
      argTys := argTys.push T
  let ws ← argTemps f1 n
  if let some i := ws.findIdx? (· == .bot) then
    err s!"[Call] argument {i + 1} is ⊥ at the call point (a later argument ended its borrow): an argument not of the parameter's type"
  if allProof then
    -- a proof is not run (P5): what it takes by `&` ends unchanged
    wholeBorrowArgs ws "an erased call"
    endBorrowArgs fuel' n 0
    setFlags (true, true)
    return (.proof, some B)
  -- [Close] with the block's text as its head: static ends' rule 1 (`lendArgs`), the row `kind`,
  -- the outputs and the fills (`closeWith`), D99 (`lendResult`)
  let g? ← lendArgs fuel' kind ws
  let r ← closeWith fuel' n 0 "a stuck block" text kind res fills argTys
  let r ← lendResult fuel' g? r (some B) "closeBlock"
  setFlags (false, false)
  modify fun s => { s with callTyLater := none }
  pure (etaUnit res r, some B)
termination_by structural fuel

/-- exp-block-text: the run of a sealed block's text (its re-run: [Seal], `nfSealed`; `split`'s
search). A block is not a function, so nothing is called: its cells are taken as a call takes its
arguments (each evaluated in order into a temporary, D115; static ends' rule 1 when its type is a
borrow, `lendArgs`), then bound in this frame, each at the declared type and reading of the place it
took (D80, D82); then the match runs in tail position, as a body does (static ends: its join, no
entry), with `B` as its hint where it reads one (D124); then the cells are dropped, most recent
first, as a frame's bindings are at its pop, the result held at `B` meanwhile (D104, D106), and a
returned borrow is ended into the reserved label (D99, `lendResult`). A stuck match is stuck:
nothing here catches it, so the program stays sealed (C5, by construction: no call is made that
could close it off). Only an untyped run meets a sealed block's text (`sealedType?` reads its type
off the text). -/
def runBlock (fuel : Nat) (typed : Bool) (cs : List (Hint × Term)) (rd : List (DeclInfo × Value))
    (pf : List Bool) (B : Value) (m : Term) : M (Value × Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  if typed then err "INTERNAL [Block] a sealed block's text is run only untyped, by its re-run (please report)"
  let n := cs.length
  let f0 ← topIdx
  for ((_, a), (_, T)) in cs.zip rd do
    demand (a matches .borrow _)
    let (w, _) ← eval fuel' false a
    pushTemp w (some T) "runBlock"
  let ws ← argTemps f0 n
  if let some i := ws.findIdx? (· == .bot) then
    err s!"[Call] argument {i + 1} is ⊥ at the call point (a later argument ended its borrow): an argument not of the parameter's type"
  let kind ← kindOf fuel' B
  let g? ← lendArgs fuel' (if kind == .prop then .data else kind) ws
  -- the cells leave the temporaries as they are bound (D115)
  let ws ← argTemps f0 n
  dropTemps f0 n
  for ((((h, _), (d, T)), p), w) in ((cs.zip rd).zip pf).zip ws.toList do
    pushBind h (some T) (etaUnit d w) p (← refineDecl d)
  let hint ← if ← readsHint fuel' true false m then pure (some B) else pure none
  modify fun s => { s with tailNext := true }
  let (v, _) ← eval fuel' false m hint
  wholeReturned v
  pushTemp v (some B) "runBlock"
  for _ in [0:n] do dropTopBind fuel'
  let v ← popTemp
  let v ← lendResult fuel' g? v (some B) "runBlock"
  setFlags (false, false)
  modify fun s => { s with callTyLater := none }
  pure (v, some B)
termination_by structural fuel

-- ### Observation and `Id` (RULES §4)

/-- `⟦t⟧^W`: on a private copy of Ω, run `t`, end every borrow, and return the result, the
final contents of the owners in `W`, and what each re-pointed binding of `refs` points to
([Obs-ref], D113) (a tuple of the machine, not a `Pair` value, D52). -/
def observe (fuel : Nat) (typed : Bool) (t : Term) (A : Value) (W : List Pos)
    (refs : List (Place × Value × Value) := []) (consumed : List Place := []) :
    M (Value × List Value × List Value) := inStatement do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- D84 [Id-typestate]: while the side runs, a borrow held outside it (by a binding or a
  -- temporary of this frame) may not end, but (D114) one held by a binding the side consumes
  let o := (← get).obsFrame
  let f ← topIdx
  let fr := (← get).env[f]!
  let mut own := []
  for y in consumed do
    let .var i := y | err s!"INTERNAL [Id-typestate] the consumed {← ppPlace y} is not a binding (please report)"
    let .bind _ j ← varPos i | err s!"INTERNAL [Id-typestate] the consumed {← ppPlace y} is not a binding (please report)"
    own := j :: own
  modify fun s => { s with obsFrame := some (f, fr.binds.size, fr.temps.size, own) }
  let (v, T) ← onFail (eval fuel' typed t A) (modify fun s => { s with obsFrame := o })      -- A: a hint for a constructor's parameters
  -- the observation itself (writing through re-pointed borrows, ending every borrow) is not the
  -- side: no frame is watched until the copy is discarded (`inStatement` restores the outer one)
  modify fun s => { s with obsFrame := none }
  expectTy fuel' "a side of Id" T A
  -- D84, D113 [Obs-ref]: each re-pointed borrow binding `y` holding `borrow_k c` is observed as
  -- [Obs-borrow] observes a borrow result: what it points to, its content `c` as the side left it,
  -- is one more component, held as a temporary (so a borrow of part of it, a second re-pointed
  -- binding's reborrow, fills it as it ends); and where it points by a fresh value, the same for
  -- both sides, put in its place in the borrow, which the owners of `loan_k` then show. The
  -- content is moved out of the borrow, not written through it: no [Access], so no reborrow of
  -- `*y` ends before the observation's ends (D84 wrote `*y := σ_y`, which overwrote what the side
  -- left in the target, unobserved, and ended a second binding's reborrow first)
  for (y, σ, Tσ) in refs do
    let .var i := y | err s!"INTERNAL [Obs-ref] the re-pointed {← ppPlace y} is not a binding (please report)"
    let pos ← varPos i
    let .borrow k c ← getAt pos
      | err s!"INTERNAL [Obs-ref] the re-pointed {← ppPlace y} holds {← getAt pos}, not a borrow (the type-state has it re-pointed and not consumed; please report)"
    let py ← ppPlace y
    fire .ObsRef fun _ => s!"{py} points to {c}, observed; {σ} put in its place"
    setAt pos (.borrow k σ)
    pushTemp c (some Tσ) "observe"
  let v ← obsResult fuel' v T none
  let cs ← popTemps refs.length
  let ws ← W.mapM getAt
  pure (v, ws, cs.toList)
termination_by structural fuel

/-- `Id A t u ≡ And(Eq A r r', And(Eq T₁ w₁ w'₁, …))` over the result, the owners in
`W = W(t, u)` and the targets of the re-pointed bindings (D113) (just `Eq A r r'` when there are
none), both sides from the same Ω on
independent copies (v2.1, D52: directly, not through a pair, so `A` may be any borrow-free
type, a proposition or a universe included). [Obs] runs each side with the typing judgement,
wherever `Id` is evaluated (D63, rule-audit item 9), the machine included (a callee's body, a
sealed program's re-run): every binding there has its declared type (D82), so a stuck match in
a side is split and closed off as a block, as when the same `Id` is formed directly. -/
def idType (fuel : Nat) (typed : Bool) (A t u : Term) : M Value := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let A' ← evalType fuel' A
  if A'.typeHasRef then err s!"Id at {A'}: A must be borrow-free (RULES §4)"
  -- D84 [Id-typestate]: both sides leave the same type-state, read from syntax and declared types
  let tsT ← withLive true (typeState fuel' t)
  let tsU ← withLive true (typeState fuel' u)
  for (what, hint, l, r) in [("moves", "clone it, or move it on both sides", tsT.moved, tsU.moved),
      ("consumes the borrow", "pass a reborrow, &*", tsT.consumed, tsU.consumed),
      ("re-points the borrow", "re-point it on both sides", tsT.repointed, tsU.repointed),
      ("leaves moved, through a borrow,", "refill it, or move it on both sides", tsT.leftOpen, tsU.leftOpen)] do
    for (side, other, a, b) in [("left", "right", l, r), ("right", "left", r, l)] do
      if let some q := jdMissing a b then
        let qs ← ppPlace q
        fire .IdTypestate fun _ => s!"the {side} side {what} {qs}"
        let hint := if hint.endsWith "&*" then hint ++ qs else hint
        err s!"[Id-typestate] the {side} side of Id {what} {qs}, the {other} side does not ({hint})"
  -- D84 [Obs-ref]: the borrow bindings both sides re-point (and do not consume), each observed
  -- through one fresh value of its borrowed type
  let mut refs : List (Place × Value × Value) := []
  for y in tsT.repointed do
    let T ← placeType fuel' y
    let .tRef T' := T | err s!"INTERNAL [Obs-ref] {← ppPlace y} : {T} is not a borrow type (please report)"
    let d ← withLive true (placeDecl fuel' [] y)
    refs := refs ++ [(y, ← absAt fuel' d.deref T', T')]
  let st ← get
  let W := footprint st.env [t, u]
  let (a, as, ca) ← observe fuel' true t A' W refs tsT.consumed
  let (b, bs, cb) ← observe fuel' true u A' W refs tsU.consumed
  -- an owner's type is its binding's, its declared type (D82)
  let Ts ← W.mapM fun p => do
    let some T ← bindTy? fuel' p
      | err s!"INTERNAL [Obs] the owner {← getAt p} has no stored type (D82: every binding has its declared type; please report)"
    pure T
  -- D113 [Obs-ref]: what each re-pointed binding points to, at the content of its declared type
  let Tc := refs.map (·.2.2)
  let comps := (A', (a, b)) :: Ts.zip (as.zip bs) ++ Tc.zip (ca.zip cb)
  -- D64 [Repack]: `Id` observes its result, owners and re-pointed targets whole
  if typed then
    for (T, (x, y)) in comps do
      repackCheck fuel' "Id observes it" x T
      repackCheck fuel' "Id observes it" y T
  let eqs ← comps.mapM fun (T, (x, y)) => mkEqM fuel' T x y
  pure (andList eqs)
termination_by structural fuel

-- ### Typing: [Def], [Split] in tail position

/-- D61: the neutral that a run of the sealed program `t` is stuck on: re-run `t` as [Seal]
does and report the content of the scrutinee of the match it stopped at, if any. -/
def stuckScrutinee (fuel : Nat) (t : Term) : M (Option Value) := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let saved ← get
  modify fun s => { s with env := #[{}], obsFrame := none, depth := s.depth + 1 }
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
  let σ ← freshAbsR fuel' T
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
each arm is checked to the end under its refinement ([Split]), and ends with the match's join
as an instance's arm does ([Join], D119). -/
def checkTail (fuel : Nat) (t : Term) (k : Value → Value → M Unit) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  -- the editor: an error here (`k`'s included) is reported at `t`, and hovering `t` shows its goal
  locatedTail t (checkTailAt fuel' t k)
termination_by structural fuel

def checkTailAt (fuel : Nat) (t : Term) (k : Value → Value → M Unit) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  match t with
  | .prim "split" [.const f, u] =>
    -- D61: `split f in u`: split the goal's stuck result of `f`, `u` in every arm (D126: the
    -- braces form `split f(ā) { arms }` is `split f in match f(ā) { arms }`, resolved so)
    let (σ, T) ← splitTarget fuel' f
    let w ← enterWorld
    match T with
    | .tNat =>
      inWorld w do
        refine fuel' σ .zero
        trace fun _ => s!"[Split] σ{σ} := 0"
        checkTail fuel' u k
      inWorld w do
        let σ' ← freshAbsR fuel' .tNat
        refine fuel' σ (.succ (.abs σ'))
        trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
        checkTail fuel' u k
    | .tInd n ps =>
      let d ← lookupInd n
      if d.declaring then err (d.declaringMsg s!"split {f}")
      for c in List.range d.ctors.length do
        inWorld w do
          let r ← ctorRefinement fuel' d ps c
          refine fuel' σ r
          trace fun _ => s!"[Split] σ{σ} := {r}"
          checkTail fuel' u k
    | _ => err s!"split {f}: its result type {T} is not an inductive type"
  | .prim "rewrite" [h, u] | .prim "rewriteR" [h, u] =>
    -- D60: in tail position the rewritten goal becomes the path's goal, so `u` may split
    let some G := (← get).goal | err "rewrite: no goal"
    let G' ← rewriteGoal fuel' (t matches .prim "rewriteR" _) h G
    modify fun s => { s with goal := some G' }
    checkTail fuel' u k
  | .letIn h u w =>
    let du ← withLive true (declOf fuel' false [] [] u)
    let (v, T) ← eval fuel' true u
    let du' ← refineDecl du
    -- D131: the binding's reading agrees with its type
    if let some T' := T then readingAgrees fuel' h T' du' v
    pushBind h T v (← getFlags).2 du'
    checkTail fuel' w fun r R => do
      let fl ← getFlags      -- the path's tail flags (dropping may normalise)
      pushTemp r (some R) "checkTail"
      dropTopBind fuel'
      setFlags fl
      k (← popTemp) R
  | .seq u w =>
    let (v, Tv) ← eval fuel' true u
    dropValue fuel' v Tv
    checkTail fuel' w k
  | .matchNat p z s =>
    natScrutinee fuel' p
    accessPath fuel' p
    accessNeutralHead fuel' p
    match ← matchContent p with
    | .zero => checkTail fuel' z (← joinCont fuel' t k)
    | .succ _ => checkTail fuel' s (← joinCont fuel' t k)
    | .abs σ =>
      -- D119: each world's arm ends as a known constructor's does, the join dropping what
      -- another arm moves ([Join], `joinCont`), so the generic call's end states are the
      -- instances' (`runBodyCore`'s tail match, `joinEnds … tail`)
      let w ← enterWorld
      inWorld w do
        refine fuel' σ .zero
        trace fun _ => s!"[Split] σ{σ} := 0"
        checkTail fuel' z (← joinCont fuel' t k)
      inWorld w do
        let σ' ← freshAbsR fuel' .tNat
        refine fuel' σ (.succ (.abs σ'))
        trace fun _ => s!"[Split] σ{σ} := S σ{σ'}"
        checkTail fuel' s (← joinCont fuel' t k)
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
        let w ← enterWorld
        for ((_, a), c) in arms.zipIdx do
          inWorld w do
            checkTail fuel' (← bindDataFields fuel' p d ps c a) k'     -- D49 (3)
      return
    accessPath fuel' p
    accessNeutralHead fuel' p
    match ← matchContent p with
    | .ind t c _ _ _ =>
      if t != ty then err s!"[Match] on {← ppPlace p}, a value of {t}, with the constructors of {ty}"
      discard (scrutType fuel' p ty)
      match arms[c]? with
      | some (_, a) =>
        -- D93: one constructor, one arm: no join
        if (← lookupInd ty).ctors.length == 1 then checkTail fuel' a k
        else checkTail fuel' a (← joinCont fuel' (.matchInd p ty arms) k)
      | none => err s!"[Match] no arm for constructor {c}"
    | .abs σ =>
      let (d, ps) ← scrutType fuel' p ty
      -- D93: an unknown of a type with one constructor is refined in place, as `evalMatchInd` does
      if d.ctors.length == 1 then
        let r ← etaInPlace fuel' σ d ps
        fire .SplitOne fun _ => s!"σ{σ} := {r} (one constructor, in place)"
        return ← checkTail fuel' t k
      -- D119: each world's arm ends with the join, as a known constructor's does (above)
      let w ← enterWorld
      for (c, (_, a)) in (List.range d.ctors.length).zip arms do
        inWorld w do
          let r ← ctorRefinement fuel' d ps c
          refine fuel' σ r
          trace fun _ => s!"[Split] σ{σ} := {r}"
          checkTail fuel' a (← joinCont fuel' t k)
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
def checkFix (fuel : Nat) (fv : Value) (cs : List Value) (t : Term)
    (capRec : Array (Option Nat) := #[]) (rd : List (DeclInfo × Value) := []) : M Unit := do
  let fuel' + 1 := fuel | exhausted "out of fuel"
  let .fix self hs ds c dec body := t | err "internal: not a fix"
  -- D136: a local function is not recursive; recursion (`by x`) is for top-level definitions
  if let some j := dec then
    unless fv matches .gfn _ do
      err s!"[Rec] {self.name} declares `by {(hs.getD j ⟨"?"⟩).name}`, but a local function is not recursive (D136): recursion is for top-level definitions. Define {self.name} at the top level, with what it uses from the enclosing body as parameters"
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
  modify fun s => { s with env := #[{}], obsFrame := none, goal := none }
  let pf ← paramFlags fuel' cs rd ds
  let (pds, cd) ← paramDecls fuel' cs rd hs ds c
  pushFrame
  pushCaps fuel' cs rd
  let mut entries := #[]
  for (((d, h), p), pd) in ((ds.zip hs).zip pf).zip pds do
    let A ← evalType fuel' d
    match A with
    | .tRef T =>
      -- D80 (R2): a parameter whose declared type reads as `Unit` (here `&Unit`: the content) is `()`
      let c ← absAt fuel' pd.deref T
      let l ← freshLoan
      modifyFrame 0 fun fr => { fr with binds := fr.binds.push { hint := ⟨s!"{h.name}°"⟩, ty := some T, val := .loan l } }
      -- D131: the parameter's reading agrees with its type and its value
      readingAgrees fuel' h A pd (.borrow l c)
      pushBind h (some A) (.borrow l c) p pd
      entries := entries.push (match c with
        | .abs σ => if T == .tNat || (T matches .tInd ..) then some σ else none
        | _ => none)
    | _ =>
      if ← isPropV fuel' A then
        readingAgrees fuel' h A pd .proof
        pushBind h (some A) .proof p (← refineDecl pd)
        entries := entries.push none
      else
        let c ← absAt fuel' pd A
        readingAgrees fuel' h A pd c
        pushBind h (some A) c p (← refineDecl pd)
        entries := entries.push (match c with
          | .abs σ => if A == .tNat || (A matches .tInd ..) then some σ else none
          | _ => none)
  let goal ← evalType fuel' c
  trace fun _ => s!"[Def] {self.name}: goal {goal}"
  let F1 ← popFrameRaw
  let piTy := Value.tPi cs (.pi hs ds c) rd
  -- D78, D136's amendment: every function's binding of itself carries a fresh mark, whether or not
  -- it recurses. The mark states a fact about the state (this binding is this function's own), which
  -- the consistency proof's relation reads to find the function in its body's frame; the checker
  -- reads it only through an entry of the [Rec] stack, which only a function with `by` has (below)
  let uid := (← get).nextRecUid
  modify fun s => { s with nextRecUid := s.nextRecUid + 1 }
  pushFrame
  pushCaps fuel' cs rd
  -- D78: a capture of an enclosing function's binding of itself keeps its mark, so a
  -- recursive call of that function from this closure's body is still recognised by name
  markCapRec capRec
  pushBind self (some piTy) fv false (.pi cd)
  markLastRec uid
  for b in F1.binds.extract cs.length F1.binds.size do pushBind b.hint b.ty b.val b.proof b.decl
  -- [Rec]: the stack holds the functions being checked that declare `by xⱼ` (v1.2, D23), which
  -- since D136 is the top-level definition being checked. A local function has no entry: it cannot
  -- name itself (D31), and no other value is it while its check is under way
  if let some j := dec then
    if (entries[j]?.join).isNone then
      err s!"`by {(hs.getD j ⟨"?"⟩).name}`: the decreasing parameter must have an inductive type (or be a borrow of one)"
    modify fun s => { s with recStack := { fn := fv, entries, cands := [j], uid } :: s.recStack }
  modify fun s => { s with goal := some goal }
  -- D53 (b): the body of a function whose calls are erased is an erased term
  -- (tracked with or without D53: K2/K3 read it too)
  let bodyCopies ← pure ((← fnClass fuel' piTy) != 0)
  withErasedIf bodyCopies <| checkTail fuel' body fun v T => do
    wholeReturned v
    bodyReturns fuel' s!"{self.name} returns it" v T [] ""
    pushTempAt ((← topIdx) - 1) v (some T) "checkFix"
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
