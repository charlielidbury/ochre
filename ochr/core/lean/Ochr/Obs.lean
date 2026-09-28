import Ochr.Env

/-!
# Places, owners and the footprint (RULES §3 paths, §4 Owners / Footprint)

The pure half of §4. The observation itself (`observe`) and `Id` (`idType`) run the
machine, so they live in `Machine.lean`.
-/

namespace Ochr

inductive Step where
  | deref | fst | snd
deriving BEq, Inhabited

/-- A place as its root variable and the steps from it, root first. -/
def Place.steps : Place → Nat × List Step
  | .var i => (i, [])
  | .deref p => let (i, s) := p.steps; (i, s ++ [.deref])
  | .fst p => let (i, s) := p.steps; (i, s ++ [.fst])
  | .snd p => let (i, s) := p.steps; (i, s ++ [.snd])

/-- One step of a path: `*` goes into the content of a borrow, `.1` into the
predecessor of `S v` or the first component of a pair, `.2` into the second. -/
def stepV : Step → Value → Option Value
  | .deref, .borrow _ w => some w
  | .fst, .succ w => some w
  | .fst, .pair a _ => some a
  | .snd, .pair _ b => some b
  | _, _ => none

def Value.follow (v : Value) : List Step → Option Value
  | [] => some v
  | s :: ss => (stepV s v).bind (·.follow ss)

/-- Update the sub-value at a path. -/
def Value.updAt (f : Value → Value) : List Step → Value → Option Value
  | [], v => some (f v)
  | .deref :: ss, .borrow l w => (Value.updAt f ss w).map (.borrow l)
  | .fst :: ss, .succ w => (Value.updAt f ss w).map .succ
  | .fst :: ss, .pair a b => (Value.updAt f ss a).map (.pair · b)
  | .snd :: ss, .pair a b => (Value.updAt f ss b).map (.pair a ·)
  | _, _ => none

/-- The value held at a position contains `borrow_ℓ` (borrows are never inside
sealed programs: only their loans are). -/
partial def Value.holdsBorrow (l : Nat) : Value → Bool
  | .borrow m w => m == l || w.holdsBorrow l
  | .succ w => w.holdsBorrow l
  | .pair a b => a.holdsBorrow l || b.holdsBorrow l
  | _ => false

/-- Take `borrow_ℓ v` out of a value: returns `v` and the value with `⊥` in its place. -/
partial def Value.takeBorrow (l : Nat) : Value → Option (Value × Value)
  | .borrow m w =>
      if m == l then some (w, .bot) else (w.takeBorrow l).map fun (c, w') => (c, .borrow m w')
  | .succ w => (w.takeBorrow l).map fun (c, w') => (c, .succ w')
  | .pair a b =>
      match a.takeBorrow l with
      | some (c, a') => some (c, .pair a' b)
      | none => (b.takeBorrow l).map fun (c, b') => (c, .pair a b')
  | _ => none

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
single-owner reading refuted by meta-model C2; counterfactual runs only). -/
def footprint (env : Env) (ts : List Term) (multi : Bool := true) : List Pos := Id.run do
  let f := env.size - 1
  let n := env[f]!.binds.size
  let mut out : List Pos := []
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
        if k == .borrow || k == .assign then
          out := out ++ ownersOfRoot
        else if isRefTy || b.val.isBorrow then
          out := out ++ ownersOfRoot
  pure (sortPos out)

/-- `A × T_W` (RULES §4; just `A` when `W` is empty). -/
def tupleType (A : Value) : List Value → Value
  | [] => A
  | Ts => .tProd A (Ts.dropLast.foldr .tProd Ts.getLast!)

def tupleVal (v : Value) : List Value → Value
  | [] => v
  | ws => .pair v (ws.dropLast.foldr .pair ws.getLast!)

end Ochr
