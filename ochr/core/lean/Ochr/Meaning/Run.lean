import Ochr.Meaning.Places
import Ochr.Meaning.Apply1

/-!
# The reference run (docs/18 Def. "reference run", the meaning of code [Q2]; docs/31 D9, D10)

`run K ρ φ hint t` is the meaning of running `t` **at the future `φ`**: a state transformer on
`SState`s returning the result's meaning at `φ` with its type (`Res := Sem × TyS`), or `none`
where the run goes wrong. It follows the machine's rules except four (docs/18): every call
applies the callee's meaning and never runs its body; before a place is read, borrowed or
matched it ends exactly the borrows the place's meaning depends on (`SState.access`); a match
on data reads the tag of the scrutinee's meaning, so nothing is stuck and nothing is split (a
match on a *free* hole, an inert loan read from `φ`, picks its arm at `φ`); `Id`, `Eq` and `J`
mean as in the model, and statements run on a copy that is thrown away.

**Per-future (D10).** A position's meaning is an `SVal`, a function of the future, so that the
borrows the run itself creates can be ended (`endLabel` = `Mean.semEnd`, fixing the future at
their labels); every *read* evaluates at the ambient `φ`, so a free label (a sealed program's
hole, an inert loan) means `φ l`. The meaning of a configuration `(Ω, t)` is then the function
`fun φ => run … φ … t (Ω's sstate)`: result and state at `φ`. The run records the labels it
makes in `shape` at the position that comes to hold the borrow (a `let`'s binding, a call's
argument slot), so `access` can end them.

Structurally recursive on the term: the only recursion into code is into subterms (a `let`'s
parts, a match's arms, a Π's or closure's domain and body terms, `mkTele`). A call applies a
meaning (`applyTele`). Recursive functions mean their guarded fixpoint by stages (docs/24 §4;
the `.fix` clause). `meanV` is `Value.mean` with the code-dependent forms given by the run
(the knot, `codeMeaning`).
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

/-- A result: the meaning at the run's future, with its type. -/
abbrev Res : Type 3 := Sem × TyS

/-- The future updated at several labels. -/
def Future.updList (φ : Future) : List (Nat × Sem) → Future
  | [] => φ
  | (l, e) :: rest => (φ.upd l e).updList rest

/-- The empty state with one empty frame and the label counter at `n` (a sealed program's run
starts above its own loans). -/
def emptyState (n : Nat) : SState := { env := [{}], shape := fun _ => none, nextLoan := n }

/-- The state with one frame holding the given bindings (a closure's code runs in it). -/
def stateOf (n : Nat) (bs : List SBinding) : SState :=
  { env := [{ binds := bs }], shape := fun _ => none, nextLoan := n }

/-- A closure's frame: its captured values at their recorded types. -/
def capsState (vs : List Sem) (tys : List (DeclInfo × TyS)) : List SBinding :=
  (vs.zip tys).map fun (v, (d, T)) => { ty := T, val := fun _ => v, decl := d }

/-- The declared-type readings of the top frame, innermost first (`Decide.placeDecl`'s scope). -/
def scopeOf (s : SState) : List DeclInfo :=
  match s.env.getLast? with
  | some fr => (fr.binds.map (·.decl)).reverse
  | none => []

/-- The state's top frame extended by bindings holding the given meanings (a Π's or a
closure's parameters at formation). -/
def extendBy (s : SState) (acc : List Sem) : SState :=
  acc.foldl (fun s a => s.pushBind { ty := .plain .err, val := fun _ => a }) s

/-- Resolve a place to its root position and path. -/
def resolve (s : SState) (p : Place) : Option (Pos × List Step) :=
  let (i, steps) := p.steps
  (s.varPos i).map (·, steps)

/-- Push a binding, recording in the shape the borrow label its type carries (the binding
holds that borrow). -/
noncomputable def pushBindShaped (s : SState) (b : SBinding) : SState :=
  match b.ty.label with
  | some l =>
    let s := s.takeLabel l
    let s' := s.pushBind b
    match s'.env.getLast? with
    | some fr => { s' with shape := fun p => if p = .bind s'.topIdx (fr.binds.length - 1) then some l else s'.shape p }
    | none => s'
  | none => s.pushBind b

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The top frame's variables holding `⊥` at the run's future (D84's `entry` set of a match). -/
noncomputable def movedPlaces (s : SState) : List Place :=
  match s.env.getLast? with
  | some fr => (List.range fr.binds.length).filterMap fun i =>
      match s.varPos i with
      | some pos => if s.valAt pos (s.closedFuture φ) = .moved then some (.var i) else none
      | none => none
  | none => []

/-- The content of a place after [Access]: its meaning at `φ` (the labels it depended on that
the run holds have been ended; what remains is read from `φ`) and its type. A projected field's
type carries no data component (`Sem.follow` yields a `TyM`): a documented gap for nested
`ps = []` values under projections. -/
noncomputable def contentOf (p : Place) : SM (Sem × TyS × Pos × List Step) := fun s =>
  match resolve s p with
  | some (pos, steps) =>
    let s := s.access pos
    match Sem.follow K.dm K.Γ (s.tyAt pos).m (s.valAt pos φ) steps with
    | some (v, T) => some ((v, if steps.isEmpty then s.tyAt pos else .plain T, pos, steps), s)
    | none => none
  | none => none

/-- Set the content of a place to a constant meaning, pointwise in the future (no access: the
caller has done it). -/
noncomputable def setContent (pos : Pos) (steps : List Step) (v : Sem) : SM PUnit := fun s =>
  let T := (s.tyAt pos).m
  let old := s.valAt pos
  match Sem.updAt K.dm K.Γ T (fun _ => v) steps (old (s.closedFuture φ)) with
  | some _ => some (⟨⟩, s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T (fun _ => v) steps (old φ')).getD .err)
  | none => none

/-- [Read]: the content; a copy leaves the place, a move leaves `moved` (D80: by the declared
reading). Reading `⊥`, or a value holding it, is an error. -/
noncomputable def readPlace (p : Place) (copy : Bool) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K φ p s
  if ¬ v.whole then none else
  if copy then some ((v, T), s) else do
    -- a move of a whole position holding a borrow carries the borrow: the position is no
    -- longer its holder; the borrow is parked in a temporary, which holds it until the result
    -- is bound (D14), and the result's type names the label
    let lab := if steps.isEmpty then s.shape pos else none
    let (⟨⟩, s) ← setContent K φ pos steps .moved s
    let s := match lab with
      | some l => (s.takeLabel l).pushTempShaped (fun _ => v) l
      | none => s
    some ((v, { T with label := lab }), s)

/-- [Borrow] `&p` with a fresh label `l`: the place now reads `l`'s final content at its path, and
the result is the old content, whole, with the label in its type (the holder's position records
it in the shape when the result is bound). -/
noncomputable def borrowPlace (p : Place) : SM Res := fun s => do
  let ((v, T, pos, steps), s) ← contentOf K φ p s
  if ¬ v.whole then none else
  let (l, s) := s.freshLoan
  let T0 := (s.tyAt pos).m
  let old := s.valAt pos
  let s := s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T0 (fun _ => φ' l) steps (old φ')).getD .err
  -- the borrow is parked in a temporary, its holder until it is bound (D14)
  let s := s.pushTempShaped (fun _ => v) l
  some ((v, { T with label := some l }), s)

/-- A call at level `L` (`Apply1.lean`): unpack the callee at its carrier and apply it along its
shape (`applyFnL`); otherwise as `callOf`. -/
noncomputable def callOfL.{u} (L : Lvl.{u}) (ps : List PiParam) (out : PiOut) (fv : Sem) (args : List Res) :
    SM Res := fun s =>
  let argSems := args.map (·.1)
  let labels := args.filterMap (·.2.label)
  -- the borrow arguments' holders (parked temporaries) are consumed by the call
  let s := labels.foldl SState.takeLabel s
  match applyFnL L ps out fv argSems with
  | some (.data r finals) =>
    let s := s.mapVals fun _ v φ' => v (φ'.updList (labels.zip finals))
    let B := match out with | .data B => B argSems | .ref U => U argSems
    some ((r, .plain B), s)
  | some (.ref U fwd back) =>
    let (k, s) := s.freshLoan
    let s := s.mapVals fun _ v φ' =>
      match L.dec U (φ' k) with
      | some x => v (φ'.updList (labels.zip (back x)))
      | none => .err
    let s := s.pushTempShaped (fun _ => L.enc U fwd) k
    some ((L.enc U fwd, ⟨U, none, some k, none⟩), s)
  | none => none

/-- A call, on the evaluated callee and arguments (docs/18 Def. "reference run", first clause):
apply the callee's meaning along its shape. For a borrow-free result each lent place's final
content is fixed to its component of the finals (the future at the argument's label); for a
result `&U`, a fresh label `k`, the result holds the forward value, and each lent place reads
its component of the backward function at the final content of `k`. A callee without a shape,
or an ill-typed application, is an error. The guard of a recursive call and a statement call's
copy are the caller's (`run`'s `.call` clause). The callee's level is read off its tag
(`Apply1.lean`: one construction for `Type₀`, `Type₁`, `Type₂`). -/
noncomputable def callOf (fv : Res) (args : List Res) : SM Res := fun s =>
  match fv.2.shape with
  | some (ps, out) =>
    match fv.1 with
    | .el0 .. => callOfL lvl0 ps out fv.1 args s
    | .el1 .. => callOfL lvl1 ps out fv.1 args s
    | .el2 .. => callOfL lvl2 ps out fv.1 args s
    | _ => none
  | none => none

/-- D84, the drop at the join, as `Machine.dropAtJoin` does it (mono-lemmas' review): every place
some arm of the match moves (`Decisions.joinMoves`, static, given the places already moved at
entry) is accessed, then set to `moved`; a place whose declared reading is copy, a proof, or a
place already `⊥` is left alone; a borrow held at a dropped root ends (`endLabel`). At a root
this is below the state before; at a field place it is a real change, so the match step lemma
is stated exact against the checker's drop, not below its input. -/
noncomputable def joinDrop (t : Term) (s : SState) : SState :=
  (K.D.joinMoves (scopeOf s) (movedPlaces φ s) t).foldl (fun s q =>
    if K.D.copy (K.D.placeDecl (scopeOf s) q) then s else
    match resolve s q with
    | some (pos, steps) =>
      let s := s.access pos
      match Sem.follow K.dm K.Γ (s.tyAt pos).m (s.valAt pos (s.closedFuture φ)) steps with
      | some (.proof, _) | some (.moved, _) | none => s
      | some _ =>
        let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
        let T := (s.tyAt pos).m
        let old := s.valAt pos
        s.setAt pos fun φ' => (Sem.updAt K.dm K.Γ T (fun _ => .moved) steps (old φ')).getD .err
    | none => s) s

/-- An observation for `Id` (docs/27 Def. 5): the side's result and, after ending every live
borrow of its copy, the meaning of every position, at the run's future. -/
noncomputable def observation (r : Res) (s : SState) : List Sem :=
  let s := s.liveLabels.foldl SState.endLabel s
  r.1 :: s.positions.map fun p => s.valAt p φ

/-- The shape of a Π-term: its parameters' and output's meanings as functions of the earlier
parameters, read in a state. Used by `.pi`, `.fix`, `.val` of a closure, and `codeMeaning`. -/
structure PiShape : Type 3 where
  ps : List PiParam
  out : PiOut

mutual
/-- The reference run of a term at the future `φ`, at the type `hint` its context expects. -/
noncomputable def run (hint : TyS) : Term → SM Res
  | .place p => fun s => readPlace K φ p (K.D.copy (K.D.placeDecl (scopeOf s) p)) s
  | .borrow p => borrowPlace K φ p
  | .assign p u => fun s => do
    let ((_, T, pos, steps), s) ← contentOf K φ p s
    let ((v, R), s) ← run T u s
    -- the old content's borrow, if the place held one, ends ([Drop]); a borrow written at a
    -- root makes the place its holder (WF1: a borrow is the whole value of a position)
    let s := if steps.isEmpty then (match s.shape pos with | some l => s.endLabel l | none => s) else s
    let (⟨⟩, s) ← setContent K φ pos steps v s
    let s := match R.label, steps with
      | some l, [] => let s := s.takeLabel l; { s with shape := fun q => if q = pos then some l else s.shape q }
      | _, _ => s
    some ((.el0 Unit (), .plain (.ty0 Unit)), s)
  | .letIn _ u w => fun s => do
    let ((v, T), s) ← run (.plain .err) u s
    let s := pushBindShaped s { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u }
    let ((r, R), s) ← run hint w s
    -- [Drop] of the binding: a borrow it holds ends, then it is forgotten
    let s := match T.label with | some l => s.endLabel l | none => s
    some ((r, R), s.dropLast)
  | .seq u w => do
    -- a discarded result holding a borrow stays parked in its temporary (D14): the borrow is
    -- ended by the access that next depends on it, or by the frame's pop
    let _ ← run (.plain .err) u
    run hint w
  | .matchNat p z u => fun s => do
    -- [Match]: the arm by the tag of the scrutinee's meaning (after [Access]); `⊥` is an error;
    -- then D84's drop at the join
    let ((v, _, _, _), s) ← contentOf K φ p s
    let arm? : Option Bool := match v.asNat with
      | some 0 => some true
      | some (_ + 1) => some false
      | none => match v with
        | .ctor "Nat" 0 [] => some true
        | .ctor "Nat" 1 _ => some false
        | _ => none
    match arm? with
    | some true => do
      let ((r, R), s) ← run hint z s
      some ((r, R), joinDrop K φ (.matchNat p z u) s)
    | some false => do
      let ((r, R), s) ← run hint u s
      some ((r, R), joinDrop K φ (.matchNat p z u) s)
    | none => none
  | .matchInd p n arms => fun s => do
    let ((v, T, _, _), s) ← contentOf K φ p s
    -- a proof scrutinee is matched by its type (D45): the one arm of a one-constructor
    -- proposition; a data scrutinee by the tag of its meaning
    let c? : Option Nat := match v with
      | .proof => if arms.length = 1 then some 0 else none
      | _ => match T.m.dataOf K.dm K.Γ with
        | some (d, ps) => (K.dm.fieldsOf d ps v).map (·.1)
        | none => none
    match c? with
    | some c => do
      let ((r, R), s) ← runArm hint c arms s
      some ((r, R), joinDrop K φ (.matchInd p n arms) s)
    | none => none
  | .tind n args => do
    match K.Γ.find? (·.name == n) with
    | some d =>
      let psM ← runParams d 0 [] args
      pure (.ty (K.dm.tyM d psM), .plain (.univ d.sort))
    | none => SM.fail
  | .ctor ty c _ ps args => do
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let psM ← runParams d 0 [] ps
      let ps' := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, ps') => if n = ty then some ps' else none | none => none)
        else some psM
      match ps' with
      | some ps' =>
        -- a constructor of a Prop-sorted inductive is a proof, `⋆` (D42); its arguments are
        -- statements
        if d.sort == 0 then
          let _ ← SM.onCopy (runFields d ps' c 0 [] args)
          pure (.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩)
        else
          let fs ← runFields d ps' c 0 [] args
          pure (K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩)
      | none => SM.fail
    | none => SM.fail
  | .const n => pure (K.C.global n)
  | .val v => fun s =>
    -- an embedded value, at the hint; a function or Π-type value carries its shape
    let T : TyS := match v with
      | .clo caps t rd | .tPi caps t rd =>
        { hint with shape := (piShapeOf (stateOf 0 (capsState (capsVals caps) (capsTys rd))) t).map fun sh => (sh.ps, sh.out) }
      | .gfn n => (K.C.global n).2
      | _ => hint
    some ((meanV hint v, T), s)
  | .sort l => pure (.ty (.univ l), .plain (.univ (sortSucc l)))
  | .pi hs ds c => fun s =>
    -- [T-Pi]: the parameters' and output's meanings as functions of the earlier parameters
    -- (`runDoms`), the carrier at the declared sort (D55, `Decisions.piSort`)
    let ps := runDoms s ds
    let out : PiOut := match c with
      | .ref U => .ref fun acc => match run (.plain .err) U (extendBy s acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
      | c => .data fun acc => match run (.plain .err) c (extendBy s acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    some ((.ty (piTyAt l ps out), ⟨.univ l, some (ps, out), none, none⟩), s)
  | .fix self hs ds c dec body => fun s =>
    -- [Closure] (D51, D53, D80): a closure means a function on its annotated domain, read off
    -- the reference run of its body in the forming frame extended by `self` and the parameters
    -- (the body's layout `[caps…, self, x̄]`). A recursive `fix` means its guarded fixpoint by
    -- stages (docs/24 §4): stage 0 binds `self` to `err`, stage `k + 1` to stage `k`'s closure,
    -- and the function at arguments whose decreasing argument has rank `r` is stage `r + 1`; so
    -- a call that does not decrease reaches stage 0 and means `err`, and `mkTele` then makes
    -- the closure mean `err`.
    let ps := runDoms s ds
    let out : PiOut := match c with
      | .ref U => .ref fun acc => match run (.plain .err) U (extendBy s acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
      | c => .data fun acc => match run (.plain .err) c (extendBy s acc) with
        | some ((v, _), _) => v.asTy
        | none => .err
    -- the carrier at the declared sort (D55, D12): `piTyAt`/`closureAt` (`Apply1.lean`)
    let l := K.D.piSort (scopeOf s) (.pi hs ds c)
    let piT := piTyAt l ps out
    let start := s.nextLoan
    let bodyAt (selfM : Sem) (args : List Sem) : Option BodyOut :=
      -- the frame: `self`, then the parameters. A borrow parameter is set up as the generic call
      -- is ([Def]): a fresh label `lᵢ`, a *cell* (a temporary of the frame: temporaries do not
      -- shift de Bruijn indices) reading `lᵢ`'s final content, and the parameter holding the
      -- content as the borrow's holder (D14). Returning the parameter returns its label.
      let s₁ := s.pushBind { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM }
      let step (sa : SState × List Sem × List Pos) (ap : Sem × PiParam) : SState × List Sem × List Pos :=
        let (s, acc, cells) := sa
        if ap.2.isRef then
          let (l, s) := s.freshLoan
          let s := s.pushTemp fun ψ => ψ l
          let cell : Pos := .temp s.topIdx (((s.env.getLast?).map (·.temps.length)).getD 1 - 1)
          let s := pushBindShaped s { ty := ⟨ap.2.dom acc, none, some l, none⟩, val := fun _ => ap.1 }
          (s, acc ++ [ap.1], cells ++ [cell])
        else
          (s.pushBind { ty := .plain (ap.2.dom acc), val := fun _ => ap.1 }, acc ++ [ap.1], cells)
      let (s₂, _, cells) := (args.zip ps).foldl step (s₁, [], [])
      let codT := match out with | .data B => B args | .ref U => U args
      match run (.plain codT) body s₂ with
      | some ((r, R), s₃) =>
        -- the frame pop ends the borrows the body made and the parameters' (their cells then
        -- read the holders' contents), except the returned borrow's, whose holder is the
        -- caller's; a borrow parameter's final content is its cell's
        let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ R.label).foldl SState.endLabel s₃
        let finals := cells.map fun c => s₄.valAt c
        some ⟨r, finals, R.label⟩
      | none => none
    let closureOf (g : List Sem → Option BodyOut) : Sem := closureAt l φ ps out g
    let stage : Nat → List Sem → Option BodyOut :=
      Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
        (fun _ gk => bodyAt (closureOf gk))
    let rankOf (args : List Sem) : Nat := match dec with
      | some j =>
        match args[j]?, (ps[j]?).map (·.dom (args.take j)) with
        | some a, some T =>
          match T.dataOf K.dm K.Γ with
          | some (d, ps') => match a.as (K.dm.car d ps') with | some x => K.dm.rank x | none => 0
          | none => match a.asNat with | some n => n | none => 0
        | _, _ => 0
      | none => 0
    let g : List Sem → Option BodyOut := match dec with
      | some _ => fun args => stage (rankOf args + 1) args
      | none => bodyAt .err
    -- forming the closure moves the captured places whose declared readings are not copy (D80)
    let s' := (Term.freeVars (.fix self hs ds c dec body)).foldl (fun s i =>
      if K.D.copy (K.D.placeDecl (scopeOf s) (.var i)) then s
      else match s.varPos i with
        | some pos => s.setAt pos fun _ => .moved
        | none => s) s
    some ((closureOf g, ⟨piT, some (ps, out), none, none⟩), s')
  | .call f args hd => fun s =>
    let fl := K.D.flags (scopeOf s) (.call f args hd)
    let body : SM Res := do
      let fv ← run (.plain .err) f
      let as ← runArgs fv.2.shape 0 [] args
      -- a proof call is never applied: its value is `⋆` (P5; `Machine.callFn` at class 2); its
      -- type, the proposition, is the codomain at the arguments
      if fl.2 then
        pure (.proof, match fv.2.shape with
          | some (ps, .data B) => if as.length = ps.length then .plain (B (as.map (·.1))) else .plain .err
          | _ => .plain .err)
      else callOf fv as
    -- a statement call runs on a copy that is thrown away (E1; `Decisions.flags`, aligned)
    if fl.1 then SM.onCopy body s else body s
  | .nat => pure (.ty (.ty0 Nat), .plain (.univ 1))
  | .unit => pure (.ty (.ty0 Unit), .plain (.univ 1))
  | .zero => pure (.el0 Nat 0, .plain (.ty0 Nat))
  | .tt => pure (.el0 Unit (), .plain (.ty0 Unit))
  | .succ u => do
    let (v, _) ← run (.plain (.ty0 Nat)) u
    pure (v.succ, .plain (.ty0 Nat))
  | .eq A a b => SM.onCopy do
    let (TA, _) ← run (.plain .err) A
    let T := TyS.plain TA.asTy
    let (va, _) ← SM.onCopy (run T a)
    let (vb, _) ← SM.onCopy (run T b)
    pure (.ty (.prop (va = vb)), .plain (.univ 0))
  | .cong _ _ | .prim "symm" _ | .prim "trans" _ | .prim "rewrite" _ | .prim "rewriteR" _ =>
    pure (.proof, .plain .err)
  | .ref A => do
    let (TA, _) ← run (.plain .err) A
    pure (TA, .plain (.univ 1))
  | .id A t u => fun s => do
    -- `Id` observes: each side on a copy of the state, every borrow ended, the result and every
    -- position compared (D84: moved places are definite values, so they compare too)
    let ((TA, _), _) ← SM.onCopy (run (.plain .err) A) s
    let T := TyS.plain TA.asTy
    let o₁ ← (run T t s).map fun (r, s') => observation φ r s'
    let o₂ ← (run T u s).map fun (r, s') => observation φ r s'
    some ((.ty (.prop (o₁ = o₂)), .plain (.univ 0)), s)
  | .prim "J" [A, a, b, P, h, t] => do
    -- `J` means its transported term; its endpoints, motive and proof are statements on copies
    let _ ← SM.onCopy (run (.plain .err) A)
    let _ ← SM.onCopy (run (.plain .err) a)
    let _ ← SM.onCopy (run (.plain .err) b)
    let _ ← SM.onCopy (run (.plain .err) P)
    let _ ← SM.onCopy (run (.plain .err) h)
    run hint t
  | .prim "clone" [u] | .prim "peek" [u] => match u with
    | .place p => readPlace K φ p true
    | _ => run hint u
  | .prim "inplace" [u] => run hint u
  | .prim _ _ => SM.fail
  | .ascribe u A => do
    let (TA, _) ← SM.onCopy (run (.plain .err) A)
    let T := TyS.plain TA.asTy
    let (v, R) ← run T u
    pure (v, { T with label := R.label })
termination_by structural t => t

/-- Arm `c` of a match, run at the match's expected type. -/
noncomputable def runArm (hint : TyS) (c : Nat) : List (Hint × Term) → SM Res
  | [] => SM.fail
  | (_, t) :: rest => if c = 0 then run hint t else runArm hint (c - 1) rest
termination_by structural arms => arms

/-- The parameters of a Π-term as the model reads them: each domain term's meaning as a function
of the earlier parameters' meanings, run in the forming state extended by them; `&A` marks a
borrow parameter with content type `A`. -/
noncomputable def runDoms (s : SState) : List Term → List PiParam
  | [] => []
  | .ref A :: ds =>
    ⟨true, fun acc => match run (.plain .err) A (extendBy s acc) with
      | some ((v, _), _) => v.asTy
      | none => .err⟩ :: runDoms s ds
  | d :: ds =>
    ⟨false, fun acc => match run (.plain .err) d (extendBy s acc) with
      | some ((v, _), _) => v.asTy
      | none => .err⟩ :: runDoms s ds
termination_by structural ds => ds

/-- An inductive's parameters, each at its parameter type (a statement position, on a copy). -/
noncomputable def runParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← SM.onCopy (run (.plain (K.dm.paramTy d i earlier)) a)
    let rest ← runParams d (i + 1) (earlier ++ [v]) as
    pure (v :: rest)
termination_by structural as => as

/-- A constructor's fields, each at its field type at the earlier fields. -/
noncomputable def runFields (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : List Term → SM (List Sem)
  | [] => pure []
  | a :: as => do
    let (v, _) ← run (.plain (K.dm.fieldTy d ps c i earlier)) a
    let rest ← runFields d ps c (i + 1) (earlier ++ [v]) as
    pure (v :: rest)
termination_by structural as => as

/-- A call's arguments, each at its parameter type from the callee's shape (D82, [Call-type]). -/
noncomputable def runArgs (shape : Option (List PiParam × PiOut)) (i : Nat) (earlier : List Sem) :
    List Term → SM (List Res)
  | [] => pure []
  | a :: as => do
    let T : TyS := match shape with
      | some (ps, _) => match ps[i]? with | some p => .plain (p.dom earlier) | none => .plain .err
      | none => .plain .err
    let r ← run T a
    let rest ← runArgs shape (i + 1) (earlier ++ [r.1]) as
    pure (r :: rest)
termination_by structural as => as

/-- The shape of a closure's or Π-closure's type, from its term, in the frame of its captures. -/
noncomputable def piShapeOf (s : SState) : Term → Option PiShape
  | .pi _ ds (.ref U) | .fix _ _ ds (.ref U) _ _ =>
    some ⟨runDoms s ds, .ref fun acc => match run (.plain .err) U (extendBy s acc) with
      | some ((v, _), _) => v.asTy
      | none => .err⟩
  | .pi _ ds c | .fix _ _ ds c _ _ =>
    some ⟨runDoms s ds, .data fun acc => match run (.plain .err) c (extendBy s acc) with
      | some ((v, _), _) => v.asTy
      | none => .err⟩
  | _ => none
termination_by structural t => t

/-- The meaning of a value, with the code-dependent forms given by the run itself (the knot of
`Value.mean`'s `CodeMeaning`): a sealed program is its program run from the empty state (the
label counter above its loans) at the hint; a closure or Π-closure is its term run in a frame
holding its captures at their recorded types (D51); a global is `K.C.global`. The other clauses
are `Value.mean`'s (`meanV_eq_mean`). -/
noncomputable def meanV (hint : TyS) : Value → Sem
  | .zero => .el0 Nat 0
  | .succ v => (meanV (.plain (.ty0 Nat)) v).succ
  | .unit => .el0 Unit ()
  | .gfn n => (K.C.global n).1
  | .clo caps t rd => match run (.plain .err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
    | some ((v, _), _) => v
    | none => .err
  | .borrow _ w => meanV hint w
  | .loan l => φ l
  | .bot => .moved
  | .abs σ => ρ σ
  | .sealed t => match run hint t (emptyState (t.loans.foldl max 0 + 1)) with
    | some ((v, _), _) => v
    | none => .err
  | .proof => .proof
  | .tNat => .ty (.ty0 Nat)
  | .tUnit => .ty (.ty0 Unit)
  | .tEq A a b =>
    let T := TyS.plain (meanV (.plain .err) A).asTy
    .ty (.prop (meanV T a = meanV T b))
  | .tRef A => meanV (.plain .err) A
  | .tPi caps t rd => match run (.plain .err) t (stateOf 0 (capsState (capsVals caps) (capsTys rd))) with
    | some ((v, _), _) => .ty v.asTy
    | none => .ty .err
  | .sort l => .ty (.univ l)
  | .ind ty c _ ps fs =>
    match K.Γ.find? (·.name == ty) with
    | some d =>
      let ps? := if ps.isEmpty && !d.params.isEmpty then
          (match hint.data with | some (n, ps') => if n = ty then some ps' else none | none => none)
        else some (meanParams d 0 [] ps)
      match ps? with
      | some ps' => if d.sort == 0 then .proof else K.dm.ctorM d ps' c (meanFields d ps' c 0 [] fs)
      | none => .err
    | none => .err
  | .tInd n args =>
    match K.Γ.find? (·.name == n) with
    | some d => .ty (K.dm.tyM d (meanParams d 0 [] args))
    | none => .ty .err
termination_by structural v => v

noncomputable def meanFields (d : IndDecl) (ps : List Sem) (c i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV (.plain (K.dm.fieldTy d ps c i earlier)) v
    s :: meanFields d ps c (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

noncomputable def meanParams (d : IndDecl) (i : Nat) (earlier : List Sem) : List Value → List Sem
  | [] => []
  | v :: vs =>
    let s := meanV (.plain (K.dm.paramTy d i earlier)) v
    s :: meanParams d (i + 1) (earlier ++ [s]) vs
termination_by structural vs => vs

/-- A closure's or Π-closure's captured values, each read as a value (D51). -/
noncomputable def capsVals : List Value → List Sem
  | [] => []
  | v :: vs => meanV (.plain .err) v :: capsVals vs
termination_by structural vs => vs

/-- The captures' recorded declared types, each read as a type (D82; a type is future-free). -/
noncomputable def capsTys : List (DeclInfo × Value) → List (DeclInfo × TyS)
  | [] => []
  | (d, T) :: rest => (d, .plain (meanV (.plain .err) T).asTy) :: capsTys rest
termination_by structural rest => rest
end

/-- The code meaning the run induces at `ρ` and `φ` (the knot of `Value.mean`). Its assignment
and future arguments are ignored: `Value.mean` is only ever read at the one assignment and
future of the state, which are these. -/
noncomputable def codeMeaning : CodeMeaning where
  global := K.C.global
  sealed _ _ hint t := meanV K ρ φ hint (.sealed t)
  clo _ _ caps t rd := meanV K ρ φ (.plain .err) (.clo caps t rd)
  pi _ _ caps t rd := (meanV K ρ φ (.plain .err) (.tPi caps t rd)).asTy
  paramTy _ P ws j := match P with
    | .tPi caps t rd =>
      match piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps) (capsTys K ρ φ rd))) t with
      | some sh =>
        let acc := ws.map (meanV K ρ φ (.plain .err))
        if j < sh.ps.length then .plain ((sh.ps[j]?.map (·.dom (acc.take j))).getD .err)
        else .plain (match sh.out with | .data B => B acc | .ref U => U acc)
      | none => .plain .err
    | _ => .plain .err

/-- The knot ties: `Value.mean` at the induced code meaning is `meanV`, at the run's future. By
induction on the value; every clause but the code-dependent ones is the same text. -/
theorem meanV_eq_mean (hint : TyS) (v : Value) :
    Value.mean K.dm (codeMeaning K ρ φ) K.Γ ρ φ hint v = meanV K ρ φ hint v := by
  sorry

end

end Ochr.Meaning
