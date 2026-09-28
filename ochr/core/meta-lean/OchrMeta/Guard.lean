import OchrMeta.Interp
import OchrMeta.FrameAlg

/-! # The [Rec] guard check: structural recursion on entry values

RULES v1.3 §5 [Rec]: in the body of `fix f … by xⱼ`, `f` occurs only as the head of a call, and
every recursive call passes, in position `j`, a value (or a borrow whose content is a value) that
is a *strict subterm of `xⱼ`'s entry value `σⱼ`, as refined so far* (meta-model §3.3 C3: the
check measures the entry value, so a write before the match (`Loop`) or to the pattern variable
after it (`Grow`) is seen).

**Head-only occurrence (R2) is automatic in FO.**  Functions are not values in the first-order
fragment: `Term.call f args` is the only way a name `f` occurs, and it is always the head of a
saturated call.  The R2 escapes (`Apply(f, n)`, `let g = f; g(n)`, meta-model-v1 §1.2) are not
expressible, so there is nothing to check for them.

**The checker** is a symbolic run of the body, a branching copy of the machine `exec`:
* it starts from the *generic call environment* of `f`, exactly the state `callRun` runs a body
  from: a frame binding each parameter to a fresh abstract value `σᵢ = abs i` (a borrow
  parameter `xᵢ : &T` to `borrow_i σᵢ`), above the ports frame holding `loan_i` for each borrow
  parameter (the owner places `cᵢ` of [Def]);
* [Split]: a `match` whose scrutinee's content is an abstract `σ` checks both arms, refining
  `σ := Z` resp. `σ := S σ'` (σ' fresh) in the environment (`Env.substAbs`), in values in flight,
  and in the tracked entry value.  The *rest* of the program after a non-tail match is checked
  once per arm (RULES' [Split] closes the match off and checks the rest once; for the guard,
  per-arm is what the termination argument uses, and each arm's state is an instance of the
  closed-off one);
* the entry value `σⱼ` is kept *as refined so far* (`GSt.entry`, of the form `S…S σ` or
  `S…S Z`); a value is a strict refinement-subterm of `σⱼ` iff it is a proper subterm of that;
* at a recursive call `f(ā)` (after its arguments are evaluated), the `j`-th argument's content
  (through the borrow, when parameter `j` is a borrow) must be a strict subterm of the entry
  value; the call is then *closed off* (`closeCall`: its result is the induction hypothesis),
  not unfolded;
* a call to any other function is run by the ordinary machine (`callWith (exec P n)`), so a
  callee stuck on an abstract value is closed off by [Close] as usual.  Termination of those
  callees is the business of the call order (`Ordered`: a body calls only earlier definitions,
  or itself when declared recursive);
* erased terms (a call at a proposition, an `erase` block) are *checked* on a private copy and
  then discarded (P2): the machine does not run them, so the guard is the only barrier (R1/R2).

**Rejections** (`Reason`): a recursive argument that is not a strict subterm (`recArg`, the
reason [Rec] fails), the machine's `err` (the borrow checker), and `stuck` for a run stuck on a
neutral that is not an abstract value (a sealed program, an inert loan, a projection out of an
abstract value): generalise-then-split (RULES [Split], R4) is out of scope here, so such a
program is rejected.  Sealed programs are not re-normalised after a refinement, which only makes
more matches stuck (incompleteness, not unsoundness). -/

namespace OchrMeta

/-- Apply refinements in order. -/
def Val.refineAll (rs : List (Nat × Val)) (v : Val) : Val :=
  rs.foldl (fun v r => Val.substAbs r.1 r.2 v) v

/-- `v` is a proper subterm of `e` through `S` (the only recursive constructor of the FO data
that [Split] refines with). -/
def Val.strictSub (v : Val) : Val → Bool
  | .succ e => v == e || v.strictSub e
  | _ => false

namespace Guard

/-- Why the guard check rejects a definition. -/
inductive Reason where
  /-- [Rec]: a recursive call whose decreasing argument has content `arg`, which is not a strict
  subterm of the entry value `entry` (as refined so far). -/
  | recArg (arg entry : Val)
  /-- stuck on a neutral that is not an abstract value (generalise-then-split is out of scope) -/
  | stuck
  /-- the machine's error (borrow checker, arity, borrows inside data, …) -/
  | err
  /-- out of fuel -/
  | fuel
  /-- no such definition, no body, not declared recursive, or `recPos` out of range -/
  | badDef
  deriving DecidableEq, Repr, Inhabited

inductive Verdict where
  | accept
  | reject (r : Reason)
  deriving DecidableEq, Repr, Inhabited

/-- The checker's state on one branch. -/
structure GSt where
  st : St
  /-- next fresh abstract-value id -/
  nabs : Nat
  /-- the entry value `σⱼ` of the decreasing parameter, as refined so far -/
  entry : Val
  /-- the refinements made on this branch, oldest first -/
  refs : List (Nat × Val)
  deriving Repr, Inhabited

namespace GSt
/-- The refinement `σ_a := w`, everywhere: environment, entry value, record. -/
def refine (a : Nat) (w : Val) (g : GSt) : GSt :=
  { g with st := { g.st with env := Env.substAbs a w g.st.env }, entry := Val.substAbs a w g.entry,
           refs := g.refs ++ [(a, w)] }
def withSt (g : GSt) (s : St) : GSt := { g with st := s }
end GSt

/-- The checker's result: every branch's final state and value, or the first rejection. -/
inductive GRes where
  | ok (bs : List (GSt × Val))
  | rej (r : Reason)
  deriving Inhabited

namespace GRes
def app : GRes → GRes → GRes
  | rej r, _ => rej r
  | ok _, rej r => rej r
  | ok a, ok b => ok (a ++ b)

def bindList (k : GSt → Val → GRes) : List (GSt × Val) → GRes
  | [] => ok []
  | (g, v) :: bs => (k g v).app (bindList k bs)

def bind : GRes → (GSt → Val → GRes) → GRes
  | rej r, _ => rej r
  | ok bs, k => bindList k bs

def one (g : GSt) (v : Val) : GRes := ok [(g, v)]

/-- Lift a result of the ordinary machine. -/
def lift (g : GSt) : Res → GRes
  | .ok s v => one (g.withSt s) v
  | .stuck => rej .stuck
  | .err => rej .err
  | .oof => rej .fuel

def ofOpt (g : GSt) (v : Val) : Option St → GRes
  | some s => one (g.withSt s) v
  | none => rej .err
end GRes

/-- The content the guard measures: through the borrow when the parameter is a borrow. -/
def recContent (ty : Ty) (w : Val) : Val :=
  match ty, w with
  | .ref _, .borrow _ c => c
  | _, w => w

/-- [Rec] at a recursive call of `d` with argument values `ws`: `none` when the `j`-th argument's
content is a strict subterm of the entry value `entry` (as refined so far). -/
def guardArgs (d : FunDef) (j : Nat) (entry : Val) (ws : List Val) : Option Reason :=
  match d.params[j]?, ws[j]? with
  | some (_, ty), some w =>
    let c := recContent ty w
    if c.strictSub entry then none else some (.recArg c entry)
  | _, _ => some .err

/-- `execArgs`, branching: each argument into the temporary `tmp i` of the current frame. -/
def gexecArgs (ev : GSt → Term → GRes) : Nat → GSt → List Term → GRes
  | _, g, [] => .one g .unit
  | i, g, a :: as => (ev g a).bind fun g v => gexecArgs ev (i + 1) (g.withSt (g.st.bind (.tmp i) v)) as

/-- [Assign] after its right-hand side, exactly as in `exec`. -/
def assignTail (p : Place) (v : Val) (s : St) : Res :=
  (access true p.root p.path s).bind fun s c =>
    if p.path ≠ [] ∧ v.nb ≠ 0 then .err else
    match s.setPlace p.root p.path v with
    | none => .err
    | some s => match dropVal .unit c s with
      | none => .err
      | some s => .ok s .unit

/-- [Let] after its body, exactly as in `exec`: unbind and drop. -/
def letTail (x : Var) (w : Val) (s : St) : Option St :=
  match s.unbind x with
  | none => none
  | some (c, s) => dropVal w c s

/-- The checker for the body of `f` (declared `by x_j`), clocked like `exec`.  Each clause is the
machine's, except [Split] at a match on an abstract value, the guard at a recursive call, and
erased terms checked on a private copy. -/
def gexec (P : Prog) (f : String) (j : Nat) : Nat → GSt → Term → GRes
  | 0, _, _ => .rej .fuel
  | n + 1, g, t =>
    match t with
    -- one machine step, no sub-runs
    | .read _ | .borrow _ | .zero | .unit => .lift g (exec P 1 g.st t)
    | .assign p t => (gexec P f j n g t).bind fun g v => .lift g (assignTail p v g.st)
    | .letIn x t u => (gexec P f j n g t).bind fun g v =>
        (gexec P f j n (g.withSt (g.st.bind x v)) u).bind fun g w => .ofOpt g w (letTail x w g.st)
    | .seq t u => (gexec P f j n g t).bind fun g v =>
        match dropVal .unit v g.st with
        | none => .rej .err
        | some s => gexec P f j n (g.withSt s) u
    | .succ t => (gexec P f j n g t).bind fun g v =>
        if v.nb = 0 then .one g (.succ v) else .rej .err
    -- `v` is in flight while `u` runs: refinements made by `u` apply to it too
    | .pair t u => (gexec P f j n g t).bind fun g v => (gexec P f j n g u).bind fun g' w =>
        let v := v.refineAll (g'.refs.drop g.refs.length)
        if v.nb = 0 ∧ w.nb = 0 then .one g' (.pair v w) else .rej .err
    | .mtch p tz y ts => (GRes.lift g (access false p.root p.path g.st)).bind fun g c =>
        match c with
        | .zero => gexec P f j n g tz
        | .succ _ => gexec P f j n g (ts.substVar y (.fst p))
        -- [Split]: `σ := Z` in the first arm, `σ := S σ'` (σ' fresh) in the second
        | .abs a =>
          let gz := g.refine a .zero
          let gs := ({ g with nabs := g.nabs + 1 }).refine a (.succ (.abs g.nabs))
          (gexec P f j n gz tz).app (gexec P f j n gs (ts.substVar y (.fst p)))
        | c => .rej (if c.isNeutral then .stuck else .err)
    | .call h args cc => match P.find h with
      | none => .rej .err
      | some d =>
        let k : GSt → List Val → GRes := fun g ws =>
          if h = f then
            -- [Rec]: check the decreasing argument, then close the call off (the IH)
            match guardArgs d j g.entry ws with
            | some r => .rej r
            | none => if d.ret = .prop then .one g .star else .lift g (closeCall f d ws g.st)
          else if d.ret = .prop then .one g .star
          else .lift g (callWith (exec P n) cc h d ws g.st)
        let r := (gexecArgs (gexec P f j n) 0 g args).bind fun g _ =>
          match takeTemps (List.range args.length) g.st with
          | none => .rej .err
          | some (ws, s) => k (g.withSt s) ws
        -- a call at a proposition is erased: checked on a private copy, then discarded (P2)
        if d.ret = .prop then (match r with | .rej e => .rej e | .ok _ => .one g .star) else r
    | .erase t => match gexec P f j n g t with
      | .rej e => .rej e
      | .ok _ => .one g .star

/-- The generic arguments: `σᵢ = abs i` for a value parameter, `borrow_i σᵢ` for a borrow one. -/
def genArgs : Nat → List (Var × Ty) → List Val
  | _, [] => []
  | i, (_, .ref _) :: ps => .borrow i (.abs i) :: genArgs (i + 1) ps
  | i, _ :: ps => .abs i :: genArgs (i + 1) ps

/-- The generic call state of `d` ([Def]): the state `callRun` runs the body from, at the generic
arguments: the parameter frame above the ports frame, which holds `loan_i` for each borrow
parameter (the owner places `cᵢ`). -/
def genSt (d : FunDef) : St :=
  let F := paramFrame d (genArgs 0 d.params)
  ⟨[F, Env.portsOf [F]], d.params.length⟩

/-- The initial checker state for `d` with decreasing parameter `j`. -/
def genG (d : FunDef) (j : Nat) : GSt := ⟨genSt d, d.params.length, .abs j, []⟩

/-- The branches of the check of `f`'s body: the final states and values (before the frame pop). -/
def checkRun (P : Prog) (f : String) (fuel : Nat) : Option GRes :=
  match P.find f with
  | none => none
  | some d => match d.body, d.recPos with
    | some b, some j => some (gexec P f j fuel (genG d j) b)
    | _, _ => none

/-- **The [Rec] check** of a recursive definition `f`, with fuel: run its body from the generic
call state with [Split] and the guard at every recursive call, then pop the frame ([Drop]). -/
def checkDef (P : Prog) (f : String) (fuel : Nat) : Verdict :=
  match P.find f with
  | none => .reject .badDef
  | some d => match d.body, d.recPos with
    | some b, some j =>
      if j < d.params.length then
        match gexec P f j fuel (genG d j) b with
        | .rej r => .reject r
        | .ok bs => if bs.all (fun (g, v) => (popFrame v g.st).isSome) then .accept else .reject .err
      else .reject .badDef
    | _, _ => .reject .badDef

end Guard

mutual
/-- The names of the functions a term calls. -/
def Term.calls : Term → List String
  | .read _ | .borrow _ | .zero | .unit => []
  | .assign _ t | .succ t | .erase t => t.calls
  | .letIn _ t u | .seq t u | .pair t u => t.calls ++ u.calls
  | .mtch _ tz _ ts => tz.calls ++ ts.calls
  | .call f args _ => f :: Term.callsList args
def Term.callsList : List Term → List String
  | [] => []
  | t :: ts => t.calls ++ Term.callsList ts
end

namespace Guard

/-- The call order, with `seen` the names defined so far. -/
def orderedAux : List String → Prog → Bool
  | _, [] => true
  | seen, (f, d) :: rest =>
    !seen.contains f &&
    (match d.body with
     | none => true
     | some b => b.calls.all fun g => seen.contains g || (g == f && d.recPos.isSome)) &&
    orderedAux (f :: seen) rest

/-- The call order: definition names are distinct, and each body calls only earlier definitions,
or itself when it is declared recursive (`by xⱼ`).  RULES' programs are built this way (a
definition names earlier top-level definitions, and itself only through `fix`); it rules out
mutual recursion, which the guard, checking one definition at a time, cannot see. -/
def Ordered (P : Prog) : Prop := orderedAux [] P = true

/-- A well-guarded program: ordered, and every recursive definition passes the [Rec] check. -/
def WellGuarded (P : Prog) : Prop :=
  Ordered P ∧ ∀ f d, P.find f = some d → d.recPos.isSome → ∃ fuel, checkDef P f fuel = .accept

/-- The decision procedure, at a given fuel. -/
def wellGuardedB (P : Prog) (fuel : Nat) : Bool :=
  orderedAux [] P && P.all fun (f, d) => d.recPos.isNone || checkDef P f fuel == .accept

theorem wellGuardedB_sound {P : Prog} {fuel : Nat} (h : wellGuardedB P fuel = true) :
    WellGuarded P := by
  simp only [wellGuardedB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun f d hf hrec => ⟨fuel, ?_⟩⟩
  have hmem : (f, d) ∈ P := by
    obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp hf
    simp
  have := h.2 _ hmem
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h1
  · simp_all
  · exact h1

end Guard
end OchrMeta
