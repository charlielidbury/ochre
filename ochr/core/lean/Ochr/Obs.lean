import Ochr.Rules

/-!
# Places, owners and the footprint (RULES §3 paths, §4 Owners / Footprint)

The pure half of §4. The observation itself (`observe`) and `Id` (`idType`) run the
machine, so they live in `Machine.lean`.
-/

namespace Ochr

inductive Step where
  | deref | fst | snd
  | field (f : FieldRef)
deriving BEq, Inhabited

/-- A place as its root variable and the steps from it, root first. -/
def Place.steps : Place → Nat × List Step
  | .var i => (i, [])
  | .deref p => let (i, s) := p.steps; (i, s ++ [.deref])
  | .fst p => let (i, s) := p.steps; (i, s ++ [.fst])
  | .snd p => let (i, s) := p.steps; (i, s ++ [.snd])
  | .field g p => let (i, s) := p.steps; (i, s ++ [.field g])

/-- One step of a path: `*` goes into the content of a borrow, `.1` into the
predecessor of `S v` or field 1 of a pair, `.2` into field 2 of a pair (D52: a pair is
the library inductive `Pair`, so `.1`/`.2` are its fields by position), `.g` into a field
of a value built by the field's constructor. Every field of a proof `⋆` is `⋆` (v2.0,
D45: a match on a proof binds its fields as places holding `⋆`). -/
def stepV : Step → Value → Option Value
  | .deref, .borrow _ w => some w
  | .fst, .succ w => some w
  | .fst, .ind "Pair" 0 _ _ [a, _] => some a
  | .snd, .ind "Pair" 0 _ _ [_, b] => some b
  | .field g, .ind t c _ _ fs => if t == g.ty && c == g.ctor then fs[g.idx]? else none
  | .field _, .proof => some .proof
  | s, .ghost w => (stepV s w).map .ghost     -- D53: every part of a moved value is moved
  | _, _ => none

def Value.follow (v : Value) : List Step → Option Value
  | [] => some v
  | s :: ss => (stepV s v).bind (·.follow ss)

/-- Update the sub-value at a path. -/
def Value.updAt (f : Value → Value) : List Step → Value → Option Value
  | [], v => some (f v)
  | .deref :: ss, .borrow l w => (Value.updAt f ss w).map (.borrow l)
  | .fst :: ss, .succ w => (Value.updAt f ss w).map .succ
  | .fst :: ss, .ind "Pair" 0 h ps [a, b] => (Value.updAt f ss a).map fun a' => .ind "Pair" 0 h ps [a', b]
  | .snd :: ss, .ind "Pair" 0 h ps [a, b] => (Value.updAt f ss b).map fun b' => .ind "Pair" 0 h ps [a, b']
  | .field g :: ss, .ind t c h ps fs =>
    match (if t == g.ty && c == g.ctor then fs[g.idx]? else none) with
    | some v => (Value.updAt f ss v).map fun v' => .ind t c h ps (fs.set g.idx v')
    | none => none
  | _, _ => none

/-- The value held at a position contains `borrow_ℓ` (borrows are never inside
sealed programs: only their loans are). -/
partial def Value.holdsBorrow (l : Nat) : Value → Bool
  | .borrow m w => m == l || w.holdsBorrow l
  | .succ w | .ghost w => w.holdsBorrow l
  | _ => false

/-- Take `borrow_ℓ v` out of a value: returns `v` and the value with `⊥` in its place. -/
partial def Value.takeBorrow (l : Nat) : Value → Option (Value × Value)
  | .borrow m w =>
      if m == l then some (w, .bot) else (w.takeBorrow l).map fun (c, w') => (c, .borrow m w')
  | .succ w => (w.takeBorrow l).map fun (c, w') => (c, .succ w')
  -- a ghost borrow (partly released, [Access]) ends like the borrow it was
  | .ghost w => (w.takeBorrow l).map fun (c, w') => (c, if w' == .bot then .bot else .ghost w')
  | _ => none

/-- Make `borrow_ℓ` inside a value a ghost: unusable, but still holding its loans. -/
partial def Value.ghostBorrow (l : Nat) : Value → Value
  | .borrow m w => if m == l then .ghost (.borrow m w) else .borrow m (w.ghostBorrow l)
  | .succ w => .succ (w.ghostBorrow l)
  | v => v

def findBorrow (env : Env) (l : Nat) : Option Pos :=
  (allPos env).find? fun p => (valAt env p).holdsBorrow l

/-- A loan is live when its borrow is in Ω. Inside a [Seal] run, a loan whose
borrow lives outside the run is inert (RULES §3 [Seal]). -/
def liveLoan (env : Env) (l : Nat) : Bool := (findBorrow env l).isSome

def liveLoansIn (env : Env) (v : Value) : List Nat :=
  v.loans.foldl (fun acc l => if !acc.contains l && liveLoan env l then acc ++ [l] else acc) []

def insertPos (p : Pos) : List Pos → List Pos
  | [] => [p]
  | q :: qs => if p == q then q :: qs else if p.lt q then p :: q :: qs else q :: insertPos p qs

def sortPos (ps : List Pos) : List Pos := ps.foldl (fun acc p => insertPos p acc) []

/-- `owners(ℓ)` (RULES §4): follow every occurrence of `loan_ℓ` outward. An occurrence
inside the content of `borrow_m` contributes `owners(m)`; one inside an owned value
contributes that binding. -/
partial def owners (env : Env) (l : Nat) (seen : List Nat := []) : List Pos :=
  if seen.contains l then [] else
  sortPos <| (allPos env).flatMap fun p =>
    let v := valAt env p
    if v.hasLoan l then
      match v with
      | .borrow m _ => owners env m (l :: seen)
      | _ => [p]
    else []

/-- The footprint `W(t, u)` (RULES §4). Free places of the terms that are borrowed,
assigned, or rooted at a borrow-typed variable contribute their owners: `{x}` for a
place rooted at an owned `x`, `owners(ℓ)` for one rooted at a variable holding
`borrow_ℓ`. With `multi = false` only the first owner of a hole is kept (the
single-owner reading refuted by meta-model C2; counterfactual runs only).

The owners are listed in the order the terms first write or borrow them, then those only
reached through a borrow-typed variable, not in Ω's order: closing off a match re-orders Ω (a
sealed program binds its captures in its own order, and a borrow parameter's cell is not where
the caller's is) and turns a captured place's reads into reads through a borrow, and `Id`'s
conjunction must come out the same on every path (fuzz-port's R6). -/
def footprint (env : Env) (ts : List Term) (multi : Bool := true) : List Pos := Id.run do
  let f := env.size - 1
  let n := env[f]!.binds.size
  let mut out : List Pos := []
  for writes in [true, false] do
    for t in ts do
      for (o, _, k) in t.freeOccs do
        if o < n then
          let pos := Pos.bind f (n - 1 - o)
          let b := env[f]!.binds[n - 1 - o]!
          let isRefTy := match b.ty with | some (.tRef _) => true | _ => false
          let ownersOfRoot : List Pos := match b.val with
            | .borrow m _ => let os := owners env m; if multi then os else os.take 1
            | .bot => []
            | _ => [pos]
          let counts := if writes then k == .borrow || k == .assign else isRefTy || b.val.isBorrow
          if counts then
            for q in ownersOfRoot do
              unless out.contains q do out := out ++ [q]
  pure out

end Ochr
