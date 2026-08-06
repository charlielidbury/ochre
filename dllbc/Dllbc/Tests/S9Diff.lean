import Dllbc.Program
import Dllbc.ProgMacro

/-!
# Differential v2 — whole-program simulation (§9)

Closes M8's finding B: the differential now runs CALLER+CALLEE with the real
simulation relation, so it catches wrong-value refinements — the class the M7
`constrained` bug belonged to — not merely stuckness.

The property, upgraded: for every checkFn-accepted caller, its CONCRETE final
environment (run in *executing* mode — calls run the callee's actual body) is a
σ-**instance** of some accepted SYMBOLIC path's final environment (run in
*checking* mode — calls use the §5.3/§6.1 signature rule). `instanceOf` is
first-order matching: a symbolic `sym σ` matches any concrete value
*consistently* (same σ ⟹ same value), constructors match structurally,
loans/borrows up to the canonical renumbering. This is the simulation relation
proper.

**Harness validation** (the essential part — a counterexample-finder that has
never found its counterexample is unvalidated): with the (removed, unsound)
`constrained` wire forced on, the `advance`-caller differential goes RED; with
it off, GREEN. The `advance` cursor shares `through`'s signature but writes only
the tail, so the constrained refinement (owner ← surrendered tail) is a
provably-wrong fact — exactly what the relation catches.

Result (this run): 4 callers (through / advance / choose / push shaped), all
accepted, all a σ-instance of an accepted symbolic path (GREEN). The
`advance`-caller goes RED under forced-constrained and GREEN without —
validated.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S9Diff

/-! ## The fixed callee pool, as a PREFIX (M28 σ)

    The four callees were `FnDef`s passed as `runExec`/`symEnvs`'s TABLE. They are
    `fn` statements now, and a caller gets them by being written after them — which
    is what "scope is the call table" means, and removes the last thing in this
    file that was a declaration rather than a program. Both machines still do what
    they did: the symbolic side checks a call against the callee's SIGNATURE (it is
    sealed), the concrete side runs its body. -/

def withPool (rest : Term) : Term := prog{
  fn through (b : &mut List Nat) -> &mut List Nat { b };
  fn advance (b : &mut List Nat) -> &mut List Nat { match b { Nil => b, Cons(hd, tl) => tl } };
  fn choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat { match c { True => x, False => y } };
  fn push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  %rest }

/-! ## The simulation relation: `instanceOf` -/

/-- Match a symbolic value against a concrete one, threading a σ→value
    substitution (consistency: the same σ must map to the same value).

    **Arrays are matched up to ¶1.3's fold, not structurally** (S24). A symbolic array
    can be SEGMENTED where the concrete one is a run: merge concatenates runs but
    leaves a σ body alone, so a checking-mode group release — a fresh existential at
    the segment's owed type — blocks exactly the rejoin the executing run performs.
    The two are the same value, the σ standing for the run's slice, so the relation
    splits the concrete run by the symbolic extents and matches segment-wise. This is
    §6.1's already-flagged over-approximation ("a group releases atomically where the
    concrete machine ends lazily") arriving for arrays; without the case the harness
    reports a false counterexample on the first array body it is given. -/
partial def matchVal : Val → Val → List (Nat × Val) → Option (List (Nat × Val))
  | .sym σ, cv, subst =>
    match subst.find? (·.1 == σ) with
    | some (_, v) => if v == cv then some subst else none
    | none => some ((σ, cv) :: subst)
  | .ctor "§segs" segs, .ctor "Arr" vs, subst => matchSegs segs vs subst
  | .ctor n1 a1, .ctor n2 a2, subst => if n1 == n2 then matchList a1 a2 subst else none
  | .borrowM x p, .borrowM y q, subst => if x == y then matchVal p q subst else none
  | a, b, subst => if a == b then some subst else none   -- ⊥, loanM, pure: exact (canonicalized)
where
  matchList : List Val → List Val → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | v1 :: vs1, v2 :: vs2, s => match matchVal v1 v2 s with | some s' => matchList vs1 vs2 s' | none => none
  | _, _, _ => none
  matchSegs : List Val → List Val → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | seg :: rest, vs, s =>
    match Val.asSeg? seg with
    | none => none
    | some (c, body) =>
      match Val.natOfVal? (Val.nfV 100 c) with
      | none => none                                     -- a symbolic extent cannot align a run
      | some k =>
        match matchVal body (.ctor "Arr" (vs.take k)) s with
        | some s' => matchSegs rest (vs.drop k) s'
        | none => none
  | _, _, _ => none

/-- Match two environments entry-by-entry (same names, same order). -/
def matchEnv : Env → Env → List (Nat × Val) → Option (List (Nat × Val))
  | [], [], s => some s
  | (n1, v1) :: r1, (n2, v2) :: r2, s =>
    if n1 == n2 then (match matchVal v1 v2 s with | some s' => matchEnv r1 r2 s' | none => none) else none
  | _, _, _ => none

/-- The concrete env is a σ-instance of the symbolic env. -/
def instanceOf (symEnv concEnv : Env) : Bool := (matchEnv symEnv concEnv []).isSome

/-! ## The relation, merged (M26-C)

    M26-A extended the relation a second time and, rather than folding the two
    extensions together, left them side by side with a note: `matchVal` above has
    the array-segment case but compares structurally; M26-A's `instanceOfComputed`
    computes but has no segment case; **neither is a superset of the other**, and
    a program that both carves an array and puts a σ inside arithmetic would be a
    false counterexample under either. This is the merge.

    Why a σ can now sit inside arithmetic at all: `.seal` is legal anywhere ⇒
    evaluates (§5), so a checking-mode σ faces a concrete value MID-EXPRESSION
    and not only at a call boundary or a group release — `let a = (3 : Nat);
    let b = add a 1` leaves the symbolic side holding the neutral spine
    `natRec … σ₀` where the concrete side holds `4`. Constraint 6 named this as a
    new simulation-relation case in advance; it is one.

    Two passes, and the merge is that **both** know about carves:

      1. Collect σ ↦ concrete from every position where the symbolic side IS a
         σ — descending through constructors, borrows, AND a carved `§segs` node
         faced with a concrete run, which is where the array era's σ's live.
         First binding wins; pass 2 is what catches an inconsistent one, so this
         pass needs no failure mode.
      2. Instantiate the whole symbolic environment, normalize, and compare with
         `matchVal` — so the comparison is still up to ¶1.3's fold (segments
         align against runs) but now also up to the pure fragment's own
         computation.

    One relation, both capabilities: this is `instanceOf` with *instance* read up
    to computation as well as up to the array fold. -/

/-- Pass 1. -/
partial def collectSyms : Val → Val → List (Nat × Val) → List (Nat × Val)
  | .sym σ, cv, s => if (s.find? (·.1 == σ)).isSome then s else (σ, cv) :: s
  -- THE MERGE: a carve on the symbolic side against a run on the concrete one.
  -- Without this the σ standing for a released segment is never collected, and
  -- pass 2 compares an uninstantiated `§segs` against a run.
  | .ctor "§segs" segs, .ctor "Arr" vs, s => goSegs segs vs s
  | .ctor _ a1, .ctor _ a2, s => go a1 a2 s
  | .borrowM _ p, .borrowM _ q, s => collectSyms p q s
  | _, _, s => s
where
  go : List Val → List Val → List (Nat × Val) → List (Nat × Val)
  | v1 :: vs1, v2 :: vs2, s => go vs1 vs2 (collectSyms v1 v2 s)
  | _, _, s => s
  goSegs : List Val → List Val → List (Nat × Val) → List (Nat × Val)
  | seg :: rest, vs, s =>
    match Val.asSeg? seg with
    | none => s
    | some (c, body) =>
      match Val.natOfVal? (Val.nfV 100 c) with
      | none => s                                        -- symbolic extent: cannot align
      | some k => goSegs rest (vs.drop k) (collectSyms body (.ctor "Arr" (vs.take k)) s)
  | _, _, s => s

/-- Pass 2's substitution. Concrete values carry no σ, so one sweep is a
    fixpoint; `nfV` is what makes the comparison up to computation. -/
def instantiateSyms (subst : List (Nat × Val)) (v : Val) : Val :=
  Val.nfV 2000 (subst.foldl (fun acc kv => substSym kv.1 kv.2 acc) v)

/-- **The relation**: the concrete env is a σ-instance of the symbolic one, up to
    the array fold and up to computation. -/
def instanceOfC (symEnv concEnv : Env) : Bool :=
  let subst := (symEnv.zip concEnv).foldl (fun s p => collectSyms p.1.2 p.2.2 s) []
  symEnv.length == concEnv.length
    && (matchEnv (symEnv.map (fun p => (p.1, instantiateSyms subst p.2))) concEnv []).isSome

/-! ## The two runs and the differential check -/

/-- Executing mode: run a body concretely (calls run callee bodies), returning
    the caller's own final Ω (frame vars id ≥ 10000 filtered out). -/
def runExec (body : Term) : Except String Env :=
  match (readR defaultFuel body).run { initSt with executing := true } with
  | .ok _ st => .ok (canonicalize (st.env.filter (fun kv =>
      kv.1.id < FnMacro.progBase && kv.1.id < 10000)))
  | .error e _ => .error e

/-- Checking mode: the accepted symbolic paths' final environments. -/
def symEnvs (body : Term) : List (Except String Env) :=
  (explore defaultFuel (pushContinuations body) initSt).map
    (fun r => r.map (fun p => canonicalize (p.2.env.filter (fun kv =>
      kv.1.id < FnMacro.progBase && kv.1.id < 10000))))

/-- The differential: the concrete final env is an instance of some symbolic
    path's final env. -/
def diffV2 (body : Term) : Bool :=
  match runExec body with
  | .error _ => false
  | .ok concEnv => (symEnvs body).any (fun r => match r with
      | .ok se => instanceOf se concEnv
      | .error _ => false)

/-- The differential under the MERGED relation (M26-C). Same property, a relation
    that no longer reports a false counterexample on a program that carves *and*
    computes. -/
def diffC (body : Term) : Bool :=
  match runExec body with
  | .error _ => false
  | .ok concEnv => (symEnvs body).any (fun r => match r with
      | .ok se => instanceOfC se concEnv
      | .error _ => false)

/-! ## Callers (each demands ALL its owners, so both runs fully collapse) -/

/-- The choose caller from §6.1, demanding BOTH owners. -/
def chooseCaller : Term := withPool (prog{
  let a = 0; let b = 0; let pa = &mut a; let pb = &mut b;
  let r = choose(True, pa, pb);
  *r := 7;
  let za = a; let zb = b;
  () })

/-- A push caller. -/
def pushCaller : Term := withPool (prog{
  let x = Cons(1, Nil); let b = &mut x; push(7, b); let y = x; () })

/-! ## The property, over the caller set -/

def callers : List Term :=
  [ withPool (prog{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = through(b); *r := Cons(9, Nil); let y = x; () }),
    withPool (prog{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () }),
    chooseCaller,
    pushCaller ]

-- A caller IS a program, callees and all (M28 σ): no wrapper, no table.
def accepted : List Term := callers.filter (fun b => progOk b)

-- Every accepted caller's concrete run is a σ-instance of an accepted symbolic
-- path — the whole-program simulation theorem, over the caller set.
example : accepted.all (fun b => diffV2 b) = true := by native_decide

/-! ## The advance caller, which the validation below is about -/

def advCallerBody : Term :=
  withPool (prog{ let x = Cons(1, Cons(2, Nil)); let b = &mut x; let r = advance(b); *r := Cons(9, Nil); let y = x; () })

-- The real behaviour: the opaque σ matches the concrete value. GREEN.
example : diffV2 advCallerBody = true := by native_decide

/-! ### The same validation, at the COMPARATOR (M28 σ)

    This validation used to reintroduce the bug to catch it: a `forceConstrained`
    flag flipped the kernel back to the unsound M7 inference and the differential
    was asserted to go RED. That was the strongest form the claim can take, and it
    cost kernel surface carried for one test — the flag and the `Group.constrained`
    field it drove — which the suite's rule no longer pays for: a test asserts a
    program's verdict, not a kernel flag's effect. Both are deleted (M28 τ).

    So the same content is stated one level down, where it needs nothing from the
    kernel. The wire's lie was specific and is writable directly: it refined the
    owner to the SURRENDERED TAIL. Here is that environment, and the honest one
    beside it, put to the relation.

    **What this keeps and what it gives up.** It keeps the exact discrimination the
    old control demonstrated — this relation says NO to that wrong refinement and
    YES to the opaque σ. It gives up the demonstration that the FINDER, driven by a
    kernel that really is buggy, arrives at that comparison at all. That is a real
    reduction in strength and is recorded as one, not glossed. -/

/-- What the removed `constrained` wire claimed: the owner recovers the tail the
    issued borrow surrendered. -/
def constrainedLie : Env := [("x", .bot), ("b", .bot), ("r", .bot), ("y", cons (nat 9) nil)]

/-- What is true: the owner recovers an opaque existential. -/
def honestSym : Env := [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)]

-- The concrete run holds `Cons 1 (Cons 9 Nil)` — the write landed in the TAIL, and
-- the head is still there. The lie is not an instance of it, under either relation.
example : (match runExec advCallerBody with
           | .ok ce => instanceOf constrainedLie ce || instanceOfC constrainedLie ce
           | .error _ => true) = false := by native_decide

-- …and the honest σ is, under both — so the refusal above is discrimination and
-- not a relation that says NO to everything.
example : (match runExec advCallerBody with
           | .ok ce => instanceOf honestSym ce && instanceOfC honestSym ce
           | .error _ => false) = true := by native_decide

/-! ### The merged relation, on this same set (M26-C)

    Three assertions, because a merged relation has to be shown to have kept both
    halves and to still be able to say NO. The array-carve half is exercised
    where the array programs live (`S26Rec`, over `S24Arrays`' callers); here is
    the σ-at-a-slot half, plus the harness validation that decides it. -/

example : accepted.all (fun b => diffC b) = true := by native_decide
-- The merged relation can still say NO, and about the same wrong refinement:
-- computation does not launder it, because pass 2 compares the INSTANTIATED value.
-- Asserted above, at the comparator, over `constrainedLie` — `instanceOfC` is one
-- of the two relations that refuses it.
example : diffC advCallerBody = true := by native_decide

end Dllbc.Tests.S9Diff
