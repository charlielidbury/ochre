import Ochr.Fuzz.Case
import Ochr.Fuzz.Canon

/-!
# Fuzzer: evaluating a statement along the two paths

* `setupParams` builds the generic environment exactly as [Def] does: a fresh owned
  cell `cᵢ ↦ loan` in frame 0 for each borrow parameter, and in frame 1 the parameters
  bound to `borrow σᵢ`, `σᵢ`, or `⋆` for propositions.
* An observation of the case is the checker's own `observe` of each side (result and
  the final content of *every* binding of frames 0 and 1, i.e. the full resolution),
  plus the `Id` type computed by the checker (`eval true (Id A t u)`).
* A refinement or instance is applied to Ω with the checker's `refine` (substitution
  plus re-normalisation), which is the environment the direct path runs from; the
  generic observation is refined with `substV`, which re-normalises sealed programs.
-/

namespace Ochr.Fuzz
open Ochr Ochr.Surface

def runSt {α : Type} (x : M α) (st : MState) : Except String (α × MState) :=
  match ((x.run st).run.run #[]).1 with
  | .ok r => .ok r
  | .error (.error m) => .error m
  | .error (.stuck _) => .error "stuck (escaped to the top)"

/-- Errors that only say the checker ran out of resources: never a disagreement. -/
def isResource (e : String) : Bool :=
  e.startsWith "out of fuel" || e.startsWith "call depth exceeded"

structure Prepared where
  globals : List GDef
  inds : List IndDecl
  stmt : Def
  rejected : List (String × String)
deriving Inhabited

/-- Resolve and check the library (a rejected declaration is left out), and resolve the
statement. -/
def prepare (cfg : Config) (fuel : Nat) (decls : List SDecl) : Except String Prepared := do
  let some sd := decls.getLast? | throw "empty program"
  let (g0, i0) := preludeState cfg     -- the library: False, True, And
  let mut globals : List GDef := g0
  let mut inds : List IndDecl := i0
  let mut rej : List (String × String) := []
  for d in decls.dropLast do
    match resolveProgram decls d with
    | .error e => rej := rej ++ [(d.name, s!"(surface) {e}")]
    | .ok it =>
      let st : MState := { globals := globals, inds := inds, cfg := cfg, fuel := fuel }
      match runSt (checkItem it) st with
      | .ok ((), st') => globals := st'.globals; inds := st'.inds
      | .error e => rej := rej ++ [(d.name, e)]
  match resolveProgram decls sd with
  | .ok (.defn d) => pure { globals := globals, inds := inds, stmt := d, rejected := rej }
  | .ok _ => throw "the statement is not a definition"
  | .error e => throw s!"(surface) {e}"

inductive PKind where
  | data
  | borrow (cell : Nat)
  | proof
deriving BEq, Inhabited

structure PInfo where
  name : String
  kind : PKind
  σ : Nat          -- the abstract value (the borrowed content for a borrow parameter)
  ty : Value       -- its type
deriving Inhabited

/-- The generic environment of [Def] for the statement's parameters, as `checkFix` builds
it: parameter types evaluated left to right, each binding carrying its declared proof flag
(`paramFlags`, D35/D42), proof parameters bound to `⋆` (D27). -/
def setupParams (d : Def) : M (Array PInfo) := do
  modify fun s => { s with env := #[{}], goal := none }
  let pf ← paramFlags [] d.doms
  pushFrame
  let mut out := #[]
  for ((dom, h), p) in (d.doms.zip d.hs).zip pf do
    let A ← evalType dom
    match A with
    | .tRef T =>
      let σ ← freshAbs T
      let l ← freshLoan
      let cell := (← get).env[0]!.binds.size
      modifyFrame 0 fun fr => { fr with binds := fr.binds.push ⟨⟨s!"{h.name}°"⟩, some T, .loan l, false⟩ }
      pushBind h (some A) (.borrow l (.abs σ)) p
      out := out.push ⟨h.name, .borrow cell, σ, T⟩
    | _ =>
      let cfg := (← get).cfg
      if cfg.p5 && cfg.proofParamsStar && (← isPropV A) then
        pushBind h (some A) .proof p
        out := out.push ⟨h.name, .proof, 0, A⟩
      else
        let σ ← freshAbs A
        pushBind h (some A) (.abs σ) p
        out := out.push ⟨h.name, .data, σ, A⟩
  pure out

/-- A proposition that computes to `False` (a conjunction with a `False` conjunct counts):
definitely false, not merely stuck (`Eq Prop P Q` between two different propositions, or
`Eq Nat 1 2` before D52's injectivity, is not `⊤` without being false). -/
partial def isFalseV : Value → Bool
  | .tInd "False" [] => true
  | .tInd "And" [a, b] => isFalseV a || isFalseV b
  | _ => false

/-- The stored types of the proof parameters (frame 1), as refined in a state: an instance
is vacuous unless each is `⊤` there (its hypotheses hold). -/
def hypsHold (st : MState) (ps : Array PInfo) : Bool := Id.run do
  let some fr := st.env[1]? | return true
  let mut i := 0
  for p in ps do
    if p.kind == .proof then
      match (fr.binds[i]?).bind (·.ty) with
      | some T => if unitTop T != vTrue then return false
      | none => return false
    i := i + 1
  pure true

/-- Every binding of Ω (the resolution observes all of them). -/
def obsPositions (env : Env) : List Pos :=
  (allPos env).filter fun | .bind .. => true | _ => false

/-- One component of the observation: 0 = lhs, 1 = rhs, 2 = the `Id` type. Returns the
value and the generalisation records the run left (sealed program ↦ σ). -/
def obsComp (st : MState) (A t u : Term) (W : List Pos) (typed : Bool) (k : Nat) :
    Except String (Value × List (Value × Nat)) :=
  let act : M Value := match k with
    | 0 => do let A' ← evalType A; observe typed t A' W
    | 1 => do let A' ← evalType A; observe typed u A' W
    | _ => do let (v, _) ← eval typed (.id A t u); pure v
  match runSt act st with
  | .ok (v, st') => .ok (v, st'.neutrals)
  | .error e => .error e

def compName : Nat → String
  | 0 => "lhs"
  | 1 => "rhs"
  | _ => "Id"

/-- Refine a value: first undo the generalisations (`σ_g := ⌈n⌉`, newest first: a
generalised σ names the closed program it replaced), then substitute; `substV`
re-normalises every sealed program the substitution reaches. -/
def refineValS (st : MState) (gens : List (Value × Nat)) (α : List (Nat × Value)) (v : Value) :
    Except String (Value × MState) :=
  let act : M Value := do
    modify fun s => { s with neutrals := [] }
    let mut v := v
    for (n, σ) in gens do v ← substV (.abs σ) n v
    for (σ, r) in α do v ← substV (.abs σ) r v
    pure v
  runSt act st

/-- `refineValS` without the final state. Its final state's `neutrals` are exactly the
generalisations re-normalisation made (a type formed inside a sealed program may split
on a sealed scrutinee), which a later completion must undo too. -/
def refineVal (st : MState) (gens : List (Value × Nat)) (α : List (Nat × Value)) (v : Value) :
    Except String Value :=
  (refineValS st gens α v).map (·.1)

end Ochr.Fuzz
