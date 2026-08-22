import Dllbc.ElabCheck
import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.Tests.Diff

/-!
# Boundaries — the function-call boundary

Tests the checker at a function call: bounds-proof arguments, the call rule,
loan groups (borrows a call entangles must end together), dependent return
types instantiated at the actuals, reborrows at call sites, and recursive
cursors. Calls are checked against signatures alone, so everything the caller
needs — proofs, loan lifetimes, dependent instantiation — must cross the
boundary through the telescope.

Each sub-suite below is scoped by its own `section`, so its `open`s do not
leak into the next.
-/

section
/-!
## Bounds proofs and the two flagship push programs

A declaration seeds a telescope, explores the body, and audits each path at
return. Monomorphic at `T := Nat` throughout. Each test is a program that
declares one function and returns `()`, checking the declaration without
calling it.
-/

open Dllbc

namespace Dllbc.Tests.S5Bound

/-! ## Pure library (types as terms) -/

/-- `VecF T n = natRec (λ_.Type) Unit (λn'. λrec. Σ(_:T). rec) n`. Lowercase
    binders throughout: a capital one would put the comptime marker `⇝` on its
    domain (`Surface.binderDom`), and this type carries no modes. -/
def vecFT : Term := ty{
  λ (t : Type). λ (n : Nat).
    natRec (λ (m : Nat). Type) Unit (λ (n' : Nat). λ (rec : Type). Σ (x : t). rec) n }

/-! ## List push, by take and rebuild -/

-- `push (e : Nat, v : &mut List Nat) { let tail = *v; *v := Cons(e, tail); () }`
-- — take the payload, rebuild with the new head, write it back. The audit sees
-- `Cons σₑ σ` convert against `List Nat`.
def pushList : Term := prog{
  fn Push (e : Nat, v : &mut List Nat) -> Unit {
    let tail = *v;
    *v := Cons(e, tail);
    ()
  };
  () }

example : progOk pushList = true := by native_decide

-- Take without refill: the borrow holds a hole (⊥) at return — a function
-- cannot return one.
example : progRejects (prog_parse {
    fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; () };
    () })
  "take without refill" = true := by native_decide

-- Pushing a `True` onto a `List Nat`: the rebuilt payload fails its owed type.
example : progRejects (prog_parse {
    fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(True, tail); () };
    () })
  "owed type" = true := by native_decide

/-! ## Vec push, in place (the dependent flagship) -/

-- `push (e, v : &mut Σ (l:Nat). VecF Nat l) { match v { Pair(l, xs) => {
--    *xs := Pair(e, *xs); *l := S(*l); () } } }` — both coupled fields updated
-- in place; the audit computes `VecF Nat (S σₗ)` under the (now concrete)
-- index and closes the pair.
def vecPush : Term := prog{
  fn Push (e : Nat, v : &mut (Σ (l : Nat). vecFT Nat l)) -> Unit {
    match v { Pair(l, xs) => { *xs := Pair(e, *xs); *l := S(*l); () } }
  };
  () }

example : progOk vecPush = true := by native_decide

-- Forget `*l := S(*l)`: the length stays σₗ while the vector became one
-- longer, so the second field is checked against the stuck type `VecF Nat σₗ`
-- and the concrete `Pair` cannot inhabit it. Rejected — dependent correctness
-- catches the forgotten length update that ownership tracking alone cannot.
example : progRejects (prog_parse {
    fn Push (e : Nat, v : &mut (Σ (l : Nat). vecFT Nat l)) -> Unit {
      match v { Pair(l, xs) => { *xs := Pair(e, *xs); () } } };
    () })
  "owed type" = true := by native_decide

-- Both write orders check: under the Σ/VecF encoding the constructor takes no
-- index argument, so the order is not forced and both are honest.
example : progOk (prog{
    fn Push (e : Nat, v : &mut (Σ (l : Nat). vecFT Nat l)) -> Unit {
      match v { Pair(l, xs) => { *l := S(*l); *xs := Pair(e, *xs); () } } };
    () }) = true := by
  native_decide

/-! ## σ-typing at branch entry, and an owned-symbolic function -/

-- A `Cons` pattern on a `&mut Nat`: the branch constructor does not belong to
-- the scrutinee's type. The `Z`/`S` branches already make the match exhaustive
-- over Nat, so it is the σ-typing check (not exhaustiveness) that catches the
-- stray `Cons` branch.
example : progRejects (prog_parse {
    fn F (b : &mut Nat) -> Unit { match b { Z => (), S(m) => (), Cons(h, t) => () } };
    () })
  "does not belong" = true := by native_decide

-- Exhaustiveness: a symbolic match must cover the scrutinee type's full
-- constructor set. is_zero missing its `S` branch is rejected.
example : progRejects (prog_parse {
    fn IsZero (n : Nat) -> Bool { match n { Z => True } };
    () })
  "non-exhaustive" = true := by native_decide

-- A borrow-mode match on `&mut List Nat` missing its `Nil` branch is rejected.
example : progRejects (prog_parse {
    fn F (v : &mut List Nat) -> Unit { match v { Cons(hd, tl) => { *hd := 0; () } } };
    () })
  "non-exhaustive" = true := by native_decide

-- `is_zero (n : Nat) → Bool`: an owned symbolic argument, both branches audited
-- against the return type.
example : progOk (prog{
    fn IsZero (n : Nat) -> Bool { match n { Z => True, S(m) => False } };
    () }) = true := by
  native_decide

end Dllbc.Tests.S5Bound
end

section
/-!
## Calls as wires

Declared functions called from bodies, checked against the signature alone
(never another body — recursion forces this). A borrow argument is consumed
and its loan annotated *owed* the type the callee promises; ending an owed
loan mints a fresh existential at that type. A wire is the degenerate loan
group: after `push(7, b)`, reading the owner back gives a fresh σ typed
`List Nat`, not `Cons 7 (Cons 1 Nil)` — the imprecision is the point, the spec
is the type.

The recursive cursor `zero_all` passes the tail borrow as an argument to the
recursive call, so the call's loan is annotated owed and the audit's collapse
mints the existential — no overwrite and nothing to ghost.
-/

open Dllbc
open Dllbc.Val (nat)

namespace Dllbc.Tests.S6Call

/-- `push (e : Nat, v : &mut List Nat)`, as a prefix: everything below is
    written as `withPush (prog{ … })` and gets `push` in scope. -/
def withPush (rest : Term) : Term := prog{
  fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  %rest }

/-! ## The wire: consume and promise -/

-- `push(7, b)` consumes b and annotates its loan owed `List Nat`; the later
-- `let y = x` ends the owed loan by minting a fresh σ. y is that σ, typed a
-- list — not the concrete `Cons 7 (Cons 1 Nil)`. The spec is the type.
example : tailEnv (withPush (prog_parse {
    let x = Cons(1, Nil); let b = &m x; Push(7, b); let y = x; () }))
  [("x", .bot), ("b", .bot), ("y", .sym 0)] = true := by native_decide

/-! ## The recursive cursor -/

-- `zero_all (v : &mut List Nat) = match v { Nil => (), Cons(hd, tl) => {
--    *hd := 0; zero_all(tl); () } }` — a cursor with no decreasing argument but
-- the payload. It has no recursor form: elaborating `[k]` needs a decreasing
-- argument to recurse on, and a borrow is not one, so the declaration is
-- refused at the binding — a refused function nothing calls still fails.
-- The paid twin `S26Fuel.zeroAllF` is the same function with a fuel parameter,
-- and it checks.
def zeroAll : Term := prog_parse {
  fn ZeroAll [v] (v : &mut List Nat) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => { *hd := 0; ZeroAll(tl); () }
    } };
  () }
example : progRejects zeroAll FnMacro.fnRefusedNeedle = true := by native_decide
example : progRejects zeroAll "§12 decision 8" = true := by native_decide
example : progOk zeroAll = false := by native_decide

/-! ## Type-changing ↝ -/

-- `to_nat (v : &mut (s : Bool ↝ Nat))` — callee takes the Bool through v and
-- fills a Nat; the audit passes against the owed type Nat, not the entry Bool.
def toNatProg : Term := prog{
  fn ToNat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () };
  () }

-- Caller side: borrow a `True`, call, read the owner back — it ends as a fresh
-- σ : Nat. A strong update across a boundary, both sides. The caller is a `fn`
-- too, so what is checked is the declaration and not one run of it.
example : progOk (prog{
  fn ToNat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () };
  fn Caller () -> Nat { let x = True; let b = &m x; ToNat(b); let y = x; y };
  () }) = true := by native_decide

/-! ## Reborrow at a call site -/

-- `push(7, &mut *b)` — the reborrow Rust inserts silently; the child loan gets
-- the owed annotation and the parent recovers when it ends. Written as one
-- chain (callee and caller in the same `prog{ }`) rather than splicing a
-- caller onto `withPush`'s tail; both forms are legal, this one reads no
-- worse.
example : progOk (prog{
  fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  fn Caller () -> List Nat { let x = Cons(1, Nil); let b = &m x; Push(7, &m *b); let y = x; y };
  () }) = true := by native_decide

/-! ## Rejections -/

-- Argument type mismatch: push a `True` where a `Nat` is owed.
example : progRejects (withPush (prog_parse {
    let x = Cons(1, Nil); let b = &m x; Push(True, b); () }))
  "parameter type" = true := by native_decide

-- A non-borrow where a borrow argument is expected.
example : progRejects (withPush (prog_parse { let x = Cons(1, Nil); Push(7, x); () }))
  "expected a borrow argument" = true := by native_decide

-- Calling an unknown function.
example : progRejects (prog_parse { nope(); () }) "unknown function" = true := by native_decide

-- Using the consumed borrow variable after the call (it is ⊥).
example : progRejects (withPush (prog_parse {
    let x = Cons(1, Nil); let b = &m x; Push(7, b); let z = b; () }))
  "use-after-move" = true := by native_decide

end Dllbc.Tests.S6Call
end

section
/-!
## Entangled calls and loan groups

Some functions break the wire correspondence: `choose` returns a borrow into
`x` or `y` depending on a runtime bool, so no per-loan promise can say where a
written value lands. A call mints a loan group tying the loans it captured
to the borrows it issued: every issued borrow ends first, then the group ends
atomically, releasing each captured loan. The ordering is the soundness
argument — a captured owner cannot recover while an issued borrow lives.

The headline is the pair: the opaque group forgets (`choose` → distinct fresh
σ's; `z = 7` is not provable, and that is the cost), while the identity wire
remembers (`through` → the owner recovers the written value). A plain wire is
the degenerate `issued = []` group.
-/

open Dllbc
open Dllbc.Val (nat nil cons)

namespace Dllbc.Tests.S7Group

/-! ## `choose`: the entangled call -/

-- choose (c : Bool, x : &mut Nat, y : &mut Nat) → &mut Nat = match c { … }.
-- The callee checks under the borrow-returning audit: each branch consumes one
-- argument borrow into the result (exempt) and audits the other.
def choose : Term := prog{
  fn Choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  () }

example : progOk choose = true := by native_decide

-- After `*r := 7`, demanding `a` (via `let z = a`) forces the cascade: end
-- ℓᵣ first (its 7 surrendered and discarded — r ↦ ⊥, and 7 never reaches a or
-- b), then the group ends atomically (b's fresh existential arrives too,
-- though only a was demanded). a and b hold distinct fresh σ's; z holds a's.
-- The imprecision is the point: z = 7 is not provable.
def chooseCaller : Term := prog{
  fn Choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  let a = 0; let b = 0; let pa = &m a; let pb = &m b;
  let r = Choose(True, pa, pb);
  *r := 7;
  let z = a;
  () }

-- `let z = a` ends the group (fresh existentials for a and b) and then copies
-- a's existential, so a and z share it; canonicalization numbers a's σ first
-- (it now appears in a's own slot), b's second.
example : tailEnv chooseCaller
  [("a", .sym 0), ("b", .sym 1), ("pa", .bot), ("pb", .bot), ("r", .bot), ("z", .sym 0)]
  = true := by native_decide

/-! ## A single-borrow wire is opaque too (no signature-driven precision) -/

-- through (b : &mut List Nat) → &mut List Nat = b. It shares its signature
-- with an `advance` that returns a field reborrow of the tail — signature-only
-- checking cannot tell them apart, so constraining the captured release to the
-- surrendered payload would be unsound. Every opaque group therefore releases
-- a fresh existential: the caller below recovers a fresh σ : List Nat, not the
-- written `Cons 9 Nil`. Precision is deliberately lost for an unpinned
-- signature; `throughPin` below shows the pinned recovery route, where the
-- signature declares the wire instead of leaving it to be inferred.
def through : Term := prog{ fn Through (b : &mut List Nat) -> &mut List Nat { b }; () }

example : progOk through = true := by native_decide

def throughCaller : Term := prog{
  fn Through (b : &mut List Nat) -> &mut List Nat { b };
  let x = Cons(1, Nil); let b = &m x;
  let r = Through(b);
  *r := Cons(9, Nil);
  let y = x;
  () }

-- y is a fresh σ (the write is forgotten — deliberate, for soundness).
-- `x`'s recovered σ is typed `List Nat` (data), so reading it moves it.
example : tailEnv throughCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)] = true := by native_decide

/-- The pair that keeps the loss honest: the executing machine still writes
    the value and still hands `Cons(9, Nil)` back to the owner. What opacity
    removes is the checker's ability to know it — a fact about what was
    ascribed, not about what happens. -/
def vlist9 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S"
  [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]]]]]]]], .ctor "Nil" []]
example : (match runProgram throughCaller with
  | .ok env => env.lookup "y" == some vlist9
  | .error _ => false) = true := by native_decide

/-! ## The pinned twin: the wire, declared and checked

    `through` above shares its signature with an `advance`, so inferring the
    identity wire is unsound and the opaque release is the rule. A pin changes
    what is written, not what is inferred: `ThroughP` declares `~> *res` — "my
    captured loan's release is whatever comes back through the borrow I
    return" — and the two signatures now differ. The callee's audit checks the
    claim symbolically (fill the returned place with a fresh exit σ, convert
    against the opened pin); the caller's group end releases it with the
    surrendered payload substituted. The unpinned pair above is unaffected:
    opacity remains the default. -/

def throughPin : Term := prog{
  fn ThroughP (b : &mut (s : List Nat ~> *res)) -> &mut List Nat { b }; () }

example : progOk throughPin = true := by native_decide

def throughPinCaller : Term := prog{
  fn ThroughP (b : &mut (s : List Nat ~> *res)) -> &mut List Nat { b };
  let x = Cons(1, Nil); let b = &m x;
  let r = ThroughP(b);
  *r := Cons(9, Nil);
  let y = x;
  () }

-- y is the written value in checking mode — where `throughCaller` above gets
-- a fresh σ. A borrow-returning function has no value component to hang an
-- ensures on, so the pin is what recovers this precision.
example : tailEnv throughPinCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", vlist9)] = true := by native_decide

-- The executing counterpart: the machines now agree on the value, so the gap
-- the unpinned pair above keeps open is closed for the pinned one.
example : (match runProgram throughPinCaller with
  | .ok env => env.lookup "y" == some vlist9
  | .error _ => false) = true := by native_decide

/-! ## ⇐ demands the group exactly as ⇒ does

    Every demand collapses its group first, and overwriting a place is a
    demand on it exactly as reading one is: a captured loan's borrow is held
    by the callee, not the caller's Ω, so a write must run the same group-end
    cascade a read does. -/

-- ACCEPT: overwrite an owner whose loan a call captured. The write demands the
-- group, the group ends, the owner is released, and the write lands.
example : progOk (prog{
  fn KeepL (v : &mut List Nat) -> Unit { () };
  let a = Cons(1, Nil);
  KeepL(&m a);
  a := Cons(2, Nil);
  let y = a;
  () }) = true := by native_decide

-- ACCEPT: the same with an ISSUED borrow outstanding as well — the cascade
-- ends the issued borrow first and surrenders its payload, then releases the
-- captured owner: the group ordering, now reached from ⇐.
example : progOk (prog{
  fn Lend (v : &mut List Nat) -> &mut List Nat { &m *v };
  let a = Cons(1, Nil);
  let b = Lend(&m a);
  a := Nil;
  () }) = true := by native_decide

-- REJECT, and the exact twin of the read-driven "nothing surrendered" below:
-- `*b` was taken, so the issued borrow holds a hole and cannot surrender. The
-- demand is a WRITE here and a read there; the refusal is the same one.
example : progRejects (prog_parse {
  fn Lend (v : &mut List Nat) -> &mut List Nat { &m *v };
  let a = Cons(1, Nil);
  let b = Lend(&m a);
  let t = *b;
  a := Nil;
  () })
  "nothing surrendered" = true := by native_decide

/-! ## Rejections -/

-- The group cannot end because an issued borrow cannot surrender: `*r` was
-- taken, leaving its payload a hole (⊥), and then a captured owner is demanded.
example : progRejects (prog_parse {
  fn Choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  let a = 0; let b = 0; let pa = &m a; let pb = &m b;
  let r = Choose(True, pa, pb);
  let tk = *r;
  let z = a;
  () })
  "nothing surrendered" = true := by native_decide

-- A borrow-returning body whose returned payload fails its owed type:
-- `bad (b : &mut Nat) → &mut Bool = b` returns a Nat borrow as a Bool borrow.
example : progRejects (prog_parse { fn Bad (b : &mut Nat) -> &mut Bool { b }; () })
  "owed type" = true := by native_decide

end Dllbc.Tests.S7Group
end

section
/-!
## Dependent call-site instantiation

A call instantiates the callee's telescope at the actuals: for a pure/owned
argument, the consumed value; for a borrow argument, the actual borrow (so a
later `*b` in a type reflects the payload snapshot just passed). The remaining
parameter types, the return type, and the owed types are all read at those
actuals. Nothing downstream — lemma application, spec-carrying calls, two
recursive calls composing their specs by transitivity — works without it.

Two supporting facts: the return type is pinned at entry (a dependent return
type may mention a parameter the body consumes, so it cannot be re-read at
return), and an instantiated return or owed type may mention a caller σ, so it
must refine when that σ does.

Plus two mechanical additions: Term-level `Std` (so `Le`/`Sorted` sit at
telescope positions) and `if`-sugar over the Bool match.

A call cohort is a `fn` chain — callee above caller, which is what "a callee
is in scope by being written above its caller" means in the grammar. The
shared callees (`use_refl`, `needs`, `observe`) are written into each cohort
that uses one, rather than factored into a shared prefix — a few lines of
repetition, not a limitation.
-/

open Dllbc
open Dllbc.Std (le_reflT)

namespace Dllbc.Tests.S12Inst

/-! ## The dependent return type, instantiated at the actual -/

-- `use_refl (n : Nat) → Le n n = LeReflRaw n`. The body pure-lifts the proof
-- term `LeReflRaw n`; the audit checks it against the pinned `Le n n`.
def useRefl : Term := prog{
  fn UseRefl (n : Nat) -> Le n n { le_reflT n };
  () }
example : progOk useRefl = true := by native_decide

-- A caller returning `Le 5 5` via `use_refl(5)`: the callee's `Le n n` is
-- instantiated at `n := 5`, so the fresh existential is typed `Le 5 5`.
def callerRet : Term := prog{
  fn UseRefl (n : Nat) -> Le n n { le_reflT n };
  fn CallerRet () -> Le 5 5 { UseRefl(5) };
  () }
example : progOk callerRet = true := by native_decide

-- Symbolic actual: `f (n : Nat) → Le n n = use_refl(n)`. Instantiation substitutes
-- the caller's σ symbolically (`Le σ σ`); the pinned return type is `Le σ σ`, and
-- the returned existential is accepted at it.
def symCall : Term := prog{
  fn UseRefl (n : Nat) -> Le n n { le_reflT n };
  fn SymCall (n : Nat) -> Le n n { UseRefl(n) };
  () }
example : progOk symCall = true := by native_decide

/-! ## A dependent second parameter -/

-- `needs (a : Nat, p : Le a 2) → Unit`, the shared callee of the two cohorts
-- below. The second parameter's type must instantiate to `Le (actual) 2` BEFORE
-- `p` is checked. It is written into each cohort rather than shared: one accepts
-- and one is rejected, so they cannot be one program.

-- `needs(1, ())`: `Le 1 2` whnf's to ⊤, which `()` inhabits — accepted.
def callNeeds1 : Term := prog{
  fn Needs (a : Nat, p : Le a 2) -> Unit { () };
  fn CallNeeds1 () -> Unit { Needs(1, ()) };
  () }
example : progOk callNeeds1 = true := by native_decide

-- `needs(3, ())`: instantiation gives `Le 3 2` = ⊥, which `()` cannot inhabit —
-- REJECTED. Without instantiation the parameter type would never resolve to ⊥.
def callNeeds3 : Term := prog_parse {
  fn Needs (a : Nat, p : Le a 2) -> Unit { () };
  fn CallNeeds3 () -> Unit { Needs(3, ()) };
  () }
example : progRejects callNeeds3 "does not have its parameter type" = true := by
  native_decide

/-! ## A borrow-snapshot dependency (`*b` in a type, at a call) -/

-- `observe (b : &mut List Nat, p : Sorted (*b)) → Unit` is the shared callee of
-- both cohorts below; its second parameter's type reads the actual borrow's
-- payload snapshot at the call site.

-- Passing a borrow of `[1,2]`: `Sorted (*b)` instantiates to `Sorted [1,2]`
-- (a product of ⊤s), which the unit-pair nest inhabits — accepted.
def observeGood : Term := prog{
  fn Observe (b : &mut List Nat, p : Sorted (*b)) -> Unit { () };
  fn ObserveGood () -> Unit {
    let x = Cons(1, Cons(2, Nil));
    let bb = &m x;
    Observe(bb, Pair((), Pair((), ())));
    let y = x;
    ()
  };
  () }
example : progOk observeGood = true := by native_decide

-- Passing a borrow of `[2,1]`: `Sorted [2,1]` contains ⊥ at the first bound, so
-- the same proof fails — REJECTED. The dependent parameter caught the unsortedness.
def observeBad : Term := prog_parse {
  fn Observe (b : &mut List Nat, p : Sorted (*b)) -> Unit { () };
  fn ObserveBad () -> Unit {
    let x = Cons(2, Cons(1, Nil));
    let bb = &m x;
    Observe(bb, Pair((), Pair((), ())));
    let y = x;
    ()
  };
  () }
example : progRejects observeBad "does not have its parameter type" = true := by
  native_decide

/-! ## The σ-refinement interaction -/

-- `f (n : Nat, pf : Id Nat n 2) → Unit = { let r = use_refl(n); match pf { Refl => needsLe22(r) } }`.
-- `r` is typed `Le n n` (instantiated at the caller σ). The `Refl`-match refines
-- `n := 2`; that refinement must reach `r`'s (call-result) sctx type, turning it
-- into `Le 2 2` — which `needsLe22` then requires. Green iff the refinement
-- propagated to the instantiated call result.
def refineTest : Term := prog{
  fn UseRefl (n : Nat) -> Le n n { le_reflT n };
  fn NeedsLe22 (q : Le 2 2) -> Unit { () };
  fn RefineTest (n : Nat, pf : Id Nat n 2) -> Unit {
    let r = UseRefl(n); match pf { Refl => NeedsLe22(r) } };
  () }
example : progOk refineTest = true := by native_decide

/-! ## `if`-sugar over the Bool match -/

-- `classify (b : Bool) → Nat = if b { 1 } else { 0 }` desugars to a fresh-var let
-- and a `match` on it; a symbolic `Bool` splits into two audited paths.
def classify : Term := prog{
  fn Classify (b : Bool) -> Nat { if b { 1 } else { 0 } };
  () }
example : progOk classify = true := by native_decide

end Dllbc.Tests.S12Inst
end

section
/-!
## Bounds-proof cursors

A cursor into a list carries a bounds proof rather than a default-element
fallback: its out-of-range branch is a ⊥-conflict discharge, and an
out-of-bounds call is rejected at the call site because no proof of the false
bound exists.

The prerequisite is that borrow-mode symbolic match refines the payload
snapshot, so a parameter type mentioning `Len *v` computes per branch.

Shape decision for `nth2`: `(pij : Le (S i) j, p2 : Le (S j) (Len *v))` with
`i < j` from `pij`. Chosen over `(p1 : Le (S i) (Len *v), p2 : …)` because it
needs no third proof and no transitivity lemma: `p2` discharges `Nil`
(`Le (S j) 0 = ⊥`), `pij` discharges the `j ≤ i` branches (`Le (S i) j = ⊥`
there), the valid branch needs no proof for the head element, and both proofs
pass to the recursive call definitionally (`Le (S(S k)) (S j') ≡ Le (S k) j'`).
At concrete calls the proofs are `()` (the ⊤ inhabitant); at symbolic calls
they are parameters.
-/

open Dllbc

namespace Dllbc.Tests.S14Bounds

-- Expected concrete result Vals (test subjects).
def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]

/-! ## The segment vocabulary computes (`Len`/`Take`/`Drop`) -/

example : (Pure.nf 1000 (prog_parse { %(Std.lenFnT) %(Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]) })
    == Std.ofNat 3) = true := by native_decide
example : (Pure.nf 1000 (prog_parse { %(Std.takeFnT) %(Std.ofNat 2) %(Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]) })
    == Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2]) = true := by native_decide
example : (Pure.nf 1000 (prog_parse { %(Std.dropFnT) %(Std.ofNat 2) %(Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]) })
    == Dllbc.Std.ofList [Std.ofNat 3]) = true := by native_decide

/-! ## The cursor family, as a prefix

    `NthL`, `nth2` and `swap` are one chain: `nth2` calls `NthL`, `swap` calls
    `nth2`, and a callee is in scope by being written above its caller. Every
    caller below rides the same chain as its tail.

    `NthL (v, i, p : Le (S i) (Len *v)) → &mut Nat`. Nil: `p : Le (S i) 0 = ⊥`,
    discharged. Cons/S(k): the recursive call takes `p` unchanged — `Le (S(S k))
    (S (len *tl)) ≡ Le (S k) (len *tl)` definitionally, no lemma. `nth2` is the
    multi-issued group with two bounds proofs; `swap` is the pair, taken and
    written through. -/

def withCursors (rest : Term) : Term := prog{
  fn Nth [i] (v : &mut List Nat, i : Nat, p : Le (S i) (Len *v)) -> &mut Nat {
    match v {
      Nil => botElim Unit p,
      Cons(hd, tl) => match i {
        Z => &m *hd,
        S(k) => Nth(&m *tl, k, p)
      }
    } };
  fn Nth2 [i] (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Σ (x : &mut Nat). &mut Nat {
    match v {
      Nil => botElim Unit p2,
      Cons(hd, tl) => match i {
        Z => match j {
          Z => botElim Unit pij,
          S(jjv) => Pair(&m *hd, Nth(&m *tl, jjv, p2))
        },
        S(k) => match j {
          Z => botElim Unit pij,
          S(jj2) => Nth2(&m *tl, k, jj2, pij, p2)
        }
      }
    } };
  fn Swap (v : &mut List Nat, i : Nat, j : Nat,
                 pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Unit {
    let Pair(ei, ej) = Nth2(v, i, j, pij, p2);
    let t = *ei;
    *ei := *ej;
    *ej := t;
    () };
  %rest }

/-- All three check, as the one program they are. `nth2`'s call to `NthL` and
    `swap`'s to `nth2` are retargeted into the chain, which for `NthL`/`nth2`
    also exercises the `[i]` hoist: the decreasing parameter is second, so a
    caller writing declaration order is permuted into the sealed telescope. -/
def cursors : Term := withCursors prog_parse { () }
example : progOk cursors = true := by native_decide

/-! ## Callers — concrete proofs are `()`, OOB is a call-site rejection -/

-- `swap(bb, 0, 2, (), ())`: `Le 1 2` and `Le 3 3` both whnf to ⊤, inhabited by `()`.
def swapBody : Term := withCursors prog_parse {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  Swap(bb, 0, 2, (), ());
  let y = x;
  () }
example : progOk swapBody = true := by native_decide

#eval match Dllbc.Tests.S9Diff.runExec swapBody with
  | .ok _ => "KEEP: exec OK"
  | .error e => "KEEP: " ++ e.take 300

-- CONCRETELY: `swap(v, 0, 2)` on `[1,2,3]` yields `[3,2,1]`.
example :
    (match Dllbc.Tests.S9Diff.runExec swapBody with
     | .ok env => env.lookup "y" == some (vlist [3, 2, 1])
     | .error _ => false) = true := by native_decide

-- OUT OF BOUNDS is rejected at the CALL SITE: `swap(bb, 0, 4, (), ())` needs
-- `p2 : Le (S 4) (Len [1,2,3]) = Le 5 3 = ⊥`, and `()` cannot inhabit ⊥.
def oobBody : Term := withCursors prog_parse {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  Swap(bb, 0, 4, (), ());
  let y = x;
  () }
example : progRejects oobBody "does not have its parameter type" = true := by
  native_decide

/-! ## The multi-issued `endGroup` cascade, and a rejection -/

-- Both cursors live, then the owner is demanded: `endGroup` ends both issued
-- borrows in list order, then releases `v`.
def cascade : Term := withCursors prog_parse {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  let Pair(ei, ej) = Nth2(bb, 0, 2, (), ());
  *ei := 9; *ej := 8; let y = x; () }
example : progOk cascade = true := by native_decide

-- Take a cursor's payload (hole) then demand the owner: the group cannot end.
def rejectProbe : Term := withCursors prog_parse {
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  let Pair(ei, ej) = Nth2(bb, 0, 2, (), ());
  let taken = *ei; let y = x; () }
example : progRejects rejectProbe "nothing surrendered" = true := by native_decide

/-! ## Differential coverage — bounds-proof pool, concrete proofs by computation -/

example : Dllbc.Tests.S9Diff.diffV2 swapBody = true := by native_decide

end Dllbc.Tests.S14Bounds
end
