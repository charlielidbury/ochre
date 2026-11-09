import Ochr.Meaning.Places

/-!
# The reference run (docs/18 Def. "reference run", the meaning of code [Q2])

`run` is the meaning of running a term: a state transformer on meanings (`SState`), returning
the result's meaning as a function of the future together with its type, or `none` where the
run goes wrong. It follows the machine's rules except four (docs/18): every call applies the
callee's meaning and never runs its body; before a place is read, borrowed or matched it ends
exactly the borrows the place's meaning depends on (`SState.access`); a match on data reads
the tag of the scrutinee's meaning, so nothing is stuck and nothing is split; `Id`, `Eq` and
`J` mean as in the model, and statements run on a copy that is thrown away.

Structurally recursive on the term: the only recursion into code is into subterms (a `let`'s
parts, a match's arms, a closure's body when its meaning is *formed*, `mkTele`). A call applies
a meaning (`applyTele`). Recursive functions mean their guarded fixpoint (docs/24 §4): a call
through a function's binding of itself at an argument whose rank does not drop below the
binding's bound is an error (`SBinding.recBound`).

## Status (milestone 2, in progress)

The first-order clauses are defined. The clauses that need the whole machinery are named
holes, listed in docs/31 §"Milestone 2": `callHole` (apply the callee's Π-shape, read off its
Π-type value by running the parameter types and codomain), `fixHole` (closure formation by
`mkTele`, with the guarded fixpoint), `piHole` (Π-type formation at the declared sort),
`matchHole` (an arm by the tag, with D84's drop at the join), `idHole` (both sides on copies,
every borrow ended, every position compared), `jHole` (the transported term), `ctorHole`
(constructor values through `DataModel.ctorM` with field hints).
-/

namespace Ochr.Meaning

open Classical

/-- The run's monad: a state transformer that may fail. -/
abbrev SM (α : Type 3) : Type 3 := SState → Option (α × SState)

instance : Monad SM where
  pure a := fun s => some (a, s)
  bind x f := fun s => match x s with
    | some (a, s') => f a s'
    | none => none

def SM.fail {α : Type 3} : SM α := fun _ => none
def SM.get : SM SState := fun s => some (s, s)
def SM.set (s : SState) : SM PUnit := fun _ => some (⟨⟩, s)
def SM.modify (f : SState → SState) : SM PUnit := fun s => some (⟨⟩, f s)

/-- Run `x` on a copy of the state and discard the copy (a statement position, E1). -/
def SM.onCopy {α : Type 3} (x : SM α) : SM α := fun s => (x s).map fun (a, _) => (a, s)

/-- The context of a run: the data model, the declarations, the meanings of the globals and the
decisions read from syntax. -/
structure RunCtx : Type 3 where
  dm : DataModel
  Γ : List IndDecl
  C : CodeMeaning
  D : Decisions

/-- A type as the run knows it: its meaning, and, for a Π-type, its shape (parameters and
output), which applying a function value needs and which neither the opaque carrier nor the
value can give back (docs/31 D9). -/
structure TyS : Type 3 where
  m : TyM
  shape : Option (List PiParam × PiOut) := none

/-- A result: a meaning as a function of the future, with its type. -/
abbrev Res : Type 3 := SVal × TyS

section
variable (K : RunCtx) (ρ : Assignment)

/-- The declared-type readings of the top frame, innermost first (`Decide.placeDecl`'s scope). -/
def scopeOf (s : SState) : List DeclInfo :=
  match s.env.getLast? with
  | some fr => (fr.binds.map (·.decl)).reverse
  | none => []

/-- Resolve a place to its root position and path. -/
def resolve (s : SState) (p : Place) : Option (Pos × List Step) :=
  let (i, steps) := p.steps
  (s.varPos i).map (·, steps)

/-- The content of a place after [Access]: its meaning (future-independent, so read under the
constant future) and its type. -/
noncomputable def contentOf (p : Place) : SM (Sem × TyM × Pos × List Step) := fun s =>
  match resolve s p with
  | some (pos, steps) =>
    let s := s.access pos
    match Sem.follow K.dm K.Γ (s.tyAt pos) (s.valAt pos noFuture) steps with
    | some (v, T) => some ((v, T, pos, steps), s)
    | none => none
  | none => none

/-- Set the content of a place (no access: the caller has done it). -/
noncomputable def setContent (pos : Pos) (steps : List Step) (v : Sem) : SM PUnit := fun s =>
  match Sem.updAt K.dm K.Γ (s.tyAt pos) (fun _ => v) steps (s.valAt pos noFuture) with
  | some w => some (⟨⟩, s.setAt pos fun _ => w)
  | none => none

/-- [Read]: the content; a copy leaves the place, a move leaves `moved` (D80: by the declared
reading). Reading `⊥`, or a value holding it, is an error. -/
noncomputable def readPlace (p : Place) (copy : Bool) : SM Res := do
  let (v, T, pos, steps) ← contentOf K p
  if ¬ v.whole then SM.fail else
  if copy then pure (fun _ => v, ⟨T, none⟩) else do
    setContent K pos steps .moved
    pure (fun _ => v, ⟨T, none⟩)

/-- [Borrow] `&p` with a fresh label `l`: the place now means `l`'s final content (at the path,
inside its value), and the borrow its old content, whole. -/
noncomputable def borrowPlace (p : Place) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K p s
  if ¬ v.whole then none else
  let (l, s) := s.freshLoan
  let T0 := s.tyAt pos
  let old := s.valAt pos
  let s := s.setAt pos fun φ => (Sem.updAt K.dm K.Γ T0 (fun _ => φ l) steps (old φ)).getD .err
  some (((fun _ => v), ⟨T, none⟩), s)

/-- The holes of milestone 2 (see the module docstring). -/
noncomputable def callHole (_ : RunCtx) (_ : Assignment) (f : Res) (args : List Res) : SM Res := sorry
noncomputable def fixHole (_ : RunCtx) (_ : Assignment) (t : Term) : SM Res := sorry
noncomputable def piHole (_ : RunCtx) (_ : Assignment) (t : Term) : SM Res := sorry
noncomputable def matchHole (_ : RunCtx) (_ : Assignment) (t : Term) : SM Res := sorry
noncomputable def idHole (_ : RunCtx) (_ : Assignment) (A t u : Term) : SM Res := sorry
noncomputable def jHole (_ : RunCtx) (_ : Assignment) (args : List Term) : SM Res := sorry

/-- A constructor value from its parameters' and fields' meanings (`DataModel.ctorM`); with no
parameters written, they are read off the expected type (D8). -/
noncomputable def ctorOf (d : IndDecl) (hint : TyM) (ps fs : List Sem) (c : Nat) : Option Res :=
  let ps? := if ps.isEmpty && !d.params.isEmpty then K.dm.paramsOf d hint else some ps
  ps?.map fun ps => (fun _ => K.dm.ctorM d ps c fs, ⟨K.dm.tyM d ps, none⟩)

mutual
/-- The reference run of a term, at the type `hint` its context expects (`err` for none). -/
noncomputable def run (hint : TyM) : Term → SM Res
  | .place p => fun s =>
    readPlace K p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s
  | .borrow p => borrowPlace K p
  | .assign p u => do
    let (_, T, pos, steps) ← contentOf K p
    let (v, _) ← run T u
    setContent K pos steps (v noFuture)
    pure (fun _ => .el0 Unit (), ⟨.ty0 Unit, none⟩)
  | .letIn _ u w => fun s => do
    let ((v, T), s) ← run .err u s
    let s := s.pushBind { ty := T.m, val := v, decl := K.D.declOf (scopeOf s) u }
    let ((r, R), s) ← run hint w s
    -- [Drop] of the binding: forgetting it (its borrows end through `access` where read)
    let s := s.dropLast
    some ((r, R), s)
  | .seq u w => do
    let _ ← run .err u
    run hint w
  | .matchNat p z u => matchHole K ρ (.matchNat p z u)
  | .matchInd p n arms => matchHole K ρ (.matchInd p n arms)
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParams d 0 [] args
      pure (fun _ => .ty (K.dm.tyM d psM), ⟨.univ d.sort, none⟩)
    | none => SM.fail
  | .ctor ty c _ ps args => do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParams d 0 [] ps
      let ps' := if ps.isEmpty && !d.params.isEmpty then K.dm.paramsOf d hint else some psM
      match ps' with
      | some ps' =>
        let fs ← runFields d ps' c 0 [] args
        match ctorOf K d hint ps' fs c with
        | some r => pure r
        | none => SM.fail
      | none => SM.fail
    | none => SM.fail
  | .const n => pure (fun _ => K.C.global n, ⟨.err, none⟩)
  | .val v => pure (fun φ => Value.mean K.dm K.C K.Γ ρ φ hint v, ⟨hint, none⟩)
  | .sort l => pure (fun _ => .ty (.univ l), ⟨.univ (sortSucc l), none⟩)
  | .pi hs ds c => piHole K ρ (.pi hs ds c)
  | .fix f hs ds c d b => fixHole K ρ (.fix f hs ds c d b)
  | .call f args _ => do
    let fv ← run .err f
    let as ← runArgs fv.2.shape 0 [] args
    callHole K ρ fv as
  | .nat => pure (fun _ => .ty (.ty0 Nat), ⟨.univ 1, none⟩)
  | .unit => pure (fun _ => .ty (.ty0 Unit), ⟨.univ 1, none⟩)
  | .zero => pure (fun _ => .el0 Nat 0, ⟨.ty0 Nat, none⟩)
  | .tt => pure (fun _ => .el0 Unit (), ⟨.ty0 Unit, none⟩)
  | .succ u => do
    let (v, _) ← run (.ty0 Nat) u
    pure (fun φ => (v φ).succ, ⟨.ty0 Nat, none⟩)
  | .eq A a b => SM.onCopy do
    let (TA, _) ← run .err A
    let T := (TA noFuture).asTy
    let (va, _) ← SM.onCopy (run T a)
    let (vb, _) ← SM.onCopy (run T b)
    pure (fun φ => .ty (.prop (va φ = vb φ)), ⟨.univ 0, none⟩)
  | .cong _ _ | .prim "symm" _ | .prim "trans" _ | .prim "rewrite" _ | .prim "rewriteR" _ =>
    pure (fun _ => .proof, ⟨.err, none⟩)
  | .ref A => do
    let (TA, _) ← run .err A
    pure (TA, ⟨.univ 1, none⟩)
  | .id A t u => idHole K ρ A t u
  | .prim "J" args => jHole K ρ args
  | .prim "clone" [u] | .prim "peek" [u] => match u with
    | .place p => readPlace K p true
    | _ => run hint u
  | .prim "inplace" [u] => run hint u
  | .prim _ _ => SM.fail
  | .ascribe u A => do
    let (TA, _) ← SM.onCopy (run .err A)
    let T := (TA noFuture).asTy
    let (v, _) ← run T u
    pure (v, ⟨T, none⟩)
termination_by structural t => t

/-- An inductive's parameters, each at its parameter type (a statement position, on a copy). -/
noncomputable def runParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← SM.onCopy (run (K.dm.paramTy d i earlier) a)
    let s := v noFuture
    let rest ← runParams d (i + 1) (earlier ++ [s]) as
    pure (s :: rest)
termination_by structural as => as

/-- A constructor's fields, each at its field type at the earlier fields. -/
noncomputable def runFields (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← run (K.dm.fieldTy d ps c i earlier) a
    let s := v noFuture
    let rest ← runFields d ps c (i + 1) (earlier ++ [s]) as
    pure (s :: rest)
termination_by structural as => as

/-- A call's arguments, each at its parameter type from the callee's shape (D82, [Call-type]). -/
noncomputable def runArgs (shape : Option (List PiParam × PiOut)) (i : Nat) (earlier : List Sem) :
    List Term → SM (List Res)
  | [] => pure []
  | a :: as => do
    let T := match shape with
      | some (ps, _) => match ps[i]? with | some p => p.dom earlier | none => .err
      | none => .err
    let r ← run T a
    let rest ← runArgs shape (i + 1) (earlier ++ [r.1 noFuture]) as
    pure (r :: rest)
termination_by structural as => as
end

end

end Ochr.Meaning
