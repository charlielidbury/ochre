import Dllbc.Program
import Dllbc.ProgMacro
import Dllbc.Boundary
import Dllbc.Std
import Dllbc.Tests.Diff

/-!
# Boundaries — bounds proofs, the call rule, loan groups, dependent instantiation, cursors

**A consolidation bucket** (M28 D10). The suite grew one file per milestone, which
made a test's home a fact about WHEN it was written rather than about what it is
about. These files were merged here, in the order below, with their content moved
VERBATIM — every namespace kept, so every cross-file reference in the tree still
resolves, and each former file is fenced by a comment naming it so the git-log
archaeology survives:

  * `S5Bound.lean`
  * `S6Call.lean`
  * `S7Group.lean`
  * `S12Inst.lean`
  * `S14Bounds.lean`

Each former file's `open`s are scoped by a `section`, so nothing leaks across the
seams.
-/

-- ┌── was `Dllbc/Tests/S5Bound.lean` ──────────────────────────────────────────────
section
/-!
# §5 test suite — boundaries, and the two flagships

The milestone the calculus has been aiming at: a declaration seeds a telescope,
explores the body, and audits each path at return (§5.4). At its end the
machine is a type checker, and it checks the two flagship programs — the thing
no other artifact in this space does. Monomorphic at `T := Nat` throughout.

The headline is the **money test**: the Σ-paired `VecF` push with the length
update forgotten is REJECTED, because the pair's second field must have type
`VecF Nat σₗ` — a stuck type the concrete value cannot inhabit. Dependent
correctness catches the off-by-one that the ownership machinery alone cannot.

**Written as programs** (M28). `fn` is a statement, so each test here is a
program that declares one function and returns `()`. That is what the old
`progOkOf` did — check a declaration at its seal without calling it — said in
the one grammar instead of through a bridge.
-/

open Dllbc

namespace Dllbc.Tests.S5Bound

/-! ## Pure library (types as terms) -/

def natT : Term := .const "Nat"
def listNatT : Term := .app (.const "List") natT
/-- `VecF T n = natRec (λ_.Type) Unit (λn'. λrec. Σ(_:T). rec) n`. -/
def vecFT : Term :=
  .lam "T" .type (.lam "n" natT
    (.app (.app (.app (.app (.const "natRec") (.lam "_" natT .type)) (.const "Unit"))
      (.lam "n'" natT (.lam "rec" .type (.sigmaT "_" (.pvar "T") (.pvar "rec"))))) (.pvar "n")))
/-- `Σ (l : Nat). VecF Nat l` — the self-describing length-vector pair. -/
def sigVecF : Term := .sigmaT "l" natT (.app (.app vecFT natT) (.pvar "l"))

/-! ## §4.1 List push, by take and rebuild -/

-- `push (e : Nat, v : &mut List Nat) { let tail = *v; *v := Cons(e, tail); () }`
-- — five lines Rust rejects (E0507), accepted here: the audit sees `Cons σₑ σ`
-- convert against `List Nat`.
def pushList : Term := prog{
  fn Push (e : Nat, v : &mut List Nat) -> Unit {
    let tail = *v;
    *v := Cons(e, tail);
    ()
  };
  () }

example : progOk pushList = true := by native_decide

-- Take without refill: the borrow holds a hole (⊥) at return — a function
-- cannot return one (§5.4).
example : progRejects (prog{
    fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; () };
    () })
  "take without refill" = true := by native_decide

-- Pushing a `True` onto a `List Nat`: the rebuilt payload fails its owed type.
example : progRejects (prog{
    fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(True, tail); () };
    () })
  "owed type" = true := by native_decide

/-! ## §4.2 Vec push, in place (the dependent flagship) -/

-- `push (e, v : &mut Σ (l:Nat). VecF Nat l) { match v { Pair(l, xs) => {
--    *xs := Pair(e, *xs); *l := S(*l); () } } }` — both coupled fields updated
-- in place; the audit computes `VecF Nat (S σₗ)` under the (now concrete)
-- index and closes the pair.
def vecPush : Term := prog{
  fn Push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit {
    match v { Pair(l, xs) => { *xs := Pair(e, *xs); *l := S(*l); () } }
  };
  () }

example : progOk vecPush = true := by native_decide

-- THE MONEY TEST — forget `*l := S(*l)`: the length stays σₗ while the vector
-- became one longer, so the second field is checked against the STUCK type
-- `VecF Nat σₗ` and the concrete `Pair` cannot inhabit it. REJECTED. This is
-- dependent correctness catching the forgotten length update — the ownership
-- machinery makes the mutation safe, the dependent types make it correct.
example : progRejects (prog{
    fn Push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit {
      match v { Pair(l, xs) => { *xs := Pair(e, *xs); () } } };
    () })
  "owed type" = true := by native_decide

-- Both write orders check: under the Σ/VecF encoding the constructor takes no
-- index argument, so — per §4.2's mechanization note — the order is NOT forced
-- and both are honest (unlike the native `VCons` presentation).
example : progOk (prog{
    fn Push (e : Nat, v : &mut (Σ (l : Nat) → vecFT Nat l)) -> Unit {
      match v { Pair(l, xs) => { *l := S(*l); *xs := Pair(e, *xs); () } } };
    () }) = true := by
  native_decide

/-! ## σ-typing at branch entry, and an owned-symbolic function -/

-- A `Cons` pattern on a `&mut Nat`: the branch constructor does not belong to
-- the scrutinee's type (§3.2's seam). The `Z`/`S` branches make the match
-- exhaustive over Nat, so it is the σ-typing check (not exhaustiveness, §9)
-- that catches the stray `Cons` branch.
example : progRejects (prog{
    fn F (b : &mut Nat) -> Unit { match b { Z => (), S(m) => (), Cons(h, t) => () } };
    () })
  "does not belong" = true := by native_decide

-- Exhaustiveness (§9): a symbolic match must cover the scrutinee type's full
-- constructor set. is_zero missing its `S` branch is rejected.
example : progRejects (prog{
    fn IsZero (n : Nat) -> Bool { match n { Z => True } };
    () })
  "non-exhaustive" = true := by native_decide

-- A borrow-mode match on `&mut List Nat` missing its `Nil` branch is rejected.
example : progRejects (prog{
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
-- └── end of what was `S5Bound.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S6Call.lean` ──────────────────────────────────────────────
section
/-!
# §5.3 test suite — calls as wires

Declared functions called from bodies, checked against the SIGNATURE alone
(never another body — recursion forces this). A borrow argument is consumed
and its loan annotated *owed* the type the callee promises; ending an owed loan
mints a fresh existential at that type ("the promise is collected"). A wire is
the degenerate loan group (§6.1); groups proper are M7.

Two headline tests. **The recursive cursor** `zero_all` is §2.5's rejection's
promised counterpart: the cursor written recursively, the tail borrow passed as
an *argument* — the recursive call annotates its loan owed, and the audit's
collapse mints the existential, so no overwrite and nothing to ghost. And the
**§5.3 wire**: after `push(7, b)`, reading the owner back gives a fresh σ typed
`List Nat`, NOT `Cons 7 (Cons 1 Nil)` — the imprecision is the point, the spec
is the type.

**Written as programs** (M28 θ). `fn` is a statement, so a test is a program that
declares what it needs and then runs something. The shared callee is factored the
way any shared prefix is — a Lean function taking the rest of the block and
splicing it with `%`, which is let-chain composition and needs no mechanism.
-/

open Dllbc
open Dllbc.Val (nat)

namespace Dllbc.Tests.S6Call

/-- `push (e : Nat, v : &mut List Nat)` from §4.1/M5, as a PREFIX: everything
    below is written as `withPush (prog{ … })` and gets `push` in scope. -/
def withPush (rest : Term) : Term := prog{
  fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  %rest }

/-! ## §5.3 the wire: consume and promise -/

-- `push(7, b)` consumes b and annotates its loan owed `List Nat`; the later
-- `let y = x` ends the owed loan by minting a fresh σ. y is that σ, typed a
-- list — not the concrete `Cons 7 (Cons 1 Nil)`. "The spec is the type."
example : tailEnv (withPush (prog{
    let x = Cons(1, Nil); let b = &m x; Push(7, b); let y = x; () }))
  [("x", .bot), ("b", .bot), ("y", .sym 0)] = true := by native_decide

/-! ## The recursive cursor (§2.5's promised counterpart) -/

-- `zero_all (v : &mut List Nat) = match v { Nil => (), Cons(hd, tl) => {
--    *hd := 0; zero_all(tl); () } }` — the `[v]` payload-decrease shape, §7 cost
-- 4's own example: a cursor with no decreasing argument but the payload.
--
-- **IT HAS NO RECURSOR FORM, and the refusal is what this file asserts about it.**
-- §7 elaborates `[k]` to `natRec`/`listRec` over the parameter itself, and a borrow
-- is neither; §9's borrow-mode eliminator is FILED, not built. §12 decision 8
-- accepted the regression and blessed fuel-threading — a source change, since the
-- signature grows a parameter and a bound and every caller supplies them. The paid
-- twin is `S26Fuel.zeroAllF`, literally this function with a fuel parameter, and it
-- checks.
--
-- It was a `decl{ }` until M28 D6, because it was `S26Migrate.p6` — the whole of
-- this file's pool — and `S27Dispose` §B's residue list read the name "zero_all"
-- off it. Written as a program the decline is said directly, which is strictly more
-- than a name in a computed list: a needle no other error produces, the decision's
-- own words, and the fact that the sentinel fires at the BINDING rather than at a
-- call, so a refused function nothing calls still fails.
def zeroAll : Term := prog{
  fn ZeroAll [v] (v : &mut List Nat) -> Unit {
    match v {
      Nil => (),
      Cons(hd, tl) => { *hd := 0; ZeroAll(tl); () }
    } };
  () }
example : progRejects zeroAll FnMacro.fnRefusedNeedle = true := by native_decide
example : progRejects zeroAll "§12 decision 8" = true := by native_decide
example : progOk zeroAll = false := by native_decide

/-! ## Type-changing ↝, exercised at last -/

-- `to_nat (v : &mut (s : Bool ↝ Nat))` — callee takes the Bool through v and
-- fills a Nat; the audit passes against the OWED type Nat, not the entry Bool.
-- Named because `S27Mixed` §E asserts it too, as one of the two subjects in the
-- corpus that state a rich owed type.
def toNatProg : Term := prog{
  fn ToNat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () };
  () }
example : progOk toNatProg = true := by native_decide

-- Caller side: borrow a `True`, call, read the owner back — it ends as a fresh
-- σ : Nat. A strong update across a boundary, both sides. The caller is a `fn`
-- too, so what is checked is the declaration and not one run of it.
example : progOk (prog{
  fn ToNat (v : &mut (Bool ~> Nat)) -> Unit { *v := 0; () };
  fn Caller () -> Nat { let x = True; let b = &m x; ToNat(b); let y = x; y };
  () }) = true := by native_decide

/-! ## Reborrow at a call site -/

-- `push(7, &mut *b)` — the reborrow Rust inserts silently; the child loan gets
-- the owed annotation and the parent recovers when it ends.
--
-- Written as ONE chain rather than `withPush (prog{ fn Caller … })`: a spliced
-- tail may not declare functions, because both chains number their slots from
-- `progBase` and the inner would shadow `push`. `bindFn` refuses it — which is how
-- this line was found, having been written the wrong way first and passed green.
example : progOk (prog{
  fn Push (e : Nat, v : &mut List Nat) -> Unit { let tail = *v; *v := Cons(e, tail); () };
  fn Caller () -> List Nat { let x = Cons(1, Nil); let b = &m x; Push(7, &m *b); let y = x; y };
  () }) = true := by native_decide

/-! ## Rejections -/

-- Argument type mismatch: push a `True` where a `Nat` is owed.
example : progRejects (withPush (prog{
    let x = Cons(1, Nil); let b = &m x; Push(True, b); () }))
  "parameter type" = true := by native_decide

-- A non-borrow where a borrow argument is expected.
example : progRejects (withPush (prog{ let x = Cons(1, Nil); Push(7, x); () }))
  "expected a borrow argument" = true := by native_decide

-- Calling an unknown function.
example : progRejects (prog{ nope(); () }) "unknown function" = true := by native_decide

-- Using the consumed borrow variable after the call (it is ⊥).
example : progRejects (withPush (prog{
    let x = Cons(1, Nil); let b = &m x; Push(7, b); let z = b; () }))
  "use-after-move" = true := by native_decide

end Dllbc.Tests.S6Call
end
-- └── end of what was `S6Call.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S7Group.lean` ──────────────────────────────────────────────
section
/-!
# §6.1 test suite — entangled calls and loan groups

Some functions break the wire correspondence: `choose` returns a borrow into
`x` OR `y` depending on a runtime bool, so no per-loan promise can say where a
written value lands. A call mints a **loan group** tying the loans it captured
to the borrows it issued, and the ending discipline is the group's whole
content — every issued borrow ends first, then the group ends atomically,
releasing each captured loan. The ordering *is* the soundness argument: a
captured owner cannot recover while an issued borrow lives.

The headline is the pair: the opaque group **forgets** (choose → distinct
fresh σ's; `z = 7` is not provable, and that is the cost, §6.2), while the
identity wire **remembers** (through → the owner recovers the written value).
M5/M6's wires are now the degenerate `issued = []` group.
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

-- The §6.1 trace verbatim. After `*r := 7`, demanding `a` (via `let z = a`)
-- forces the cascade: End ℓᵣ first (its 7 surrendered and DISCARDED — the
-- ordering as soundness, r ↦ ⊥ and 7 never reaches a or b), then the group
-- ends ATOMICALLY (b's fresh existential arrives too, though only a was
-- demanded). a and b hold DISTINCT fresh σ's; z holds a's. The imprecision is
-- the point: z = 7 is not provable (§6.2's cost).
def chooseCaller : Term := prog{
  fn Choose (c : Bool, x : &mut Nat, y : &mut Nat) -> &mut Nat
    { match c { True => x, False => y } };
  let a = 0; let b = 0; let pa = &m a; let pb = &m b;
  let r = Choose(True, pa, pb);
  *r := 7;
  let z = a;
  () }

-- `let z = a` ends the group (fresh existentials for a and b) and then COPIES
-- a's existential (§2.1), so a and z share it; canonicalization numbers a's σ
-- first (it now appears in a's own slot), b's second.
example : tailEnv chooseCaller
  [("a", .sym 0), ("b", .sym 1), ("pa", .bot), ("pb", .bot), ("r", .bot), ("z", .sym 0)]
  = true := by native_decide

/-! ## A single-borrow wire is opaque too (no signature-driven precision) -/

-- through (b : &mut List Nat) → &mut List Nat = b. It shares its SIGNATURE with
-- an `advance` that returns a field reborrow of the tail — signature-only
-- checking cannot tell them apart, so constraining the captured release to the
-- surrendered payload would be UNSOUND. Every opaque group therefore releases
-- a fresh existential: the caller below recovers a FRESH σ : List Nat, NOT the
-- written `Cons 9 Nil`. Precision is deliberately lost; §6.2's transparent/spec
-- group ends are the recovery route.
def through : Term := prog{ fn Through (b : &mut List Nat) -> &mut List Nat { b }; () }

example : progOk through = true := by native_decide

def throughCaller : Term := prog{
  fn Through (b : &mut List Nat) -> &mut List Nat { b };
  let x = Cons(1, Nil); let b = &m x;
  let r = Through(b);
  *r := Cons(9, Nil);
  let y = x;
  () }

-- y is a fresh σ (the write is forgotten — deliberate, per the soundness fix).
-- `x`'s recovered σ is typed `List Nat` (DATA), so reading it MOVES it (§2.1).
example : tailEnv throughCaller
  [("x", .bot), ("b", .bot), ("r", .bot), ("y", .sym 0)] = true := by native_decide

/-- …and the pair that keeps the loss honest: the EXECUTING machine still writes
    the value and still hands `Cons(9, Nil)` back to the owner. What opacity removes
    is the CHECKER's ability to know it — §5 point 4, a fact about what was ascribed
    and never about what happens.

    Moved here from `S17Spec` when that file retired (M28 D7). §17 was the
    declared-backward-spec suite, where a `through` carrying `back = λ r. r` let the
    caller recover the written value in CHECKING mode; M27 deleted the mechanism, and
    what was left of that section was this file's own opacity claim plus this
    executing counterpart, which this file did not have. -/
def vlist9 : Val := .ctor "Cons" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S"
  [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "S" [.ctor "Z" []]]]]]]]]], .ctor "Nil" []]
example : (match runProgram throughCaller with
  | .ok env => env.lookup "y" == some vlist9
  | .error _ => false) = true := by native_decide

/-! ## ⇐ demands the group exactly as ⇒ does (M29 δ, paper finding 15)

    §5.2's rule is that every demand collapses first, and OVERWRITING a place is a
    demand on it exactly as reading one is. The two arrows used to disagree:
    `readR`'s `.var` ended a parked loan through the group-aware `endLoan`, while
    ⇐ let the marker reach `Drop`, which ends it with `killBorrowInΩ` — no group
    check — and a captured loan's borrow is by definition not an Ω entry, since
    the callee holds it. So `let y = a` after `keep(&m a)` was accepted and
    `a := 5` was refused, with "its other end is in flight".

    All three subjects below were measured under BOTH kernels. The first two moved
    from that refusal to accepting; the third moved from it to the group end's own
    audit, which is the point — the write now runs the §6.1 cascade, so it reaches
    the check that has something real to say. -/

-- ACCEPT: overwrite an owner whose loan a call captured. The write demands the
-- group, the group ends, the owner is released, and the write lands.
example : progOk (prog{
  fn KeepL (v : &mut List Nat) -> Unit { () };
  let a = Cons(1, Nil);
  KeepL(&m a);
  a := Cons(2, Nil);
  let y = a;
  () }) = true := by native_decide

-- ACCEPT: the same with an ISSUED borrow outstanding as well — the cascade ends
-- the issued borrow first and surrenders its payload, then releases the captured
-- owner, which is §6.1's ordering reached from ⇐ for the first time.
example : progOk (prog{
  fn Lend (v : &mut List Nat) -> &mut List Nat { &m *v };
  let a = Cons(1, Nil);
  let b = Lend(&m a);
  a := Nil;
  () }) = true := by native_decide

-- REJECT, and the exact twin of the read-driven "nothing surrendered" below:
-- `*b` was taken, so the issued borrow holds a hole and cannot surrender. The
-- demand is a WRITE here and a read there; the refusal is the same one.
example : progRejects (prog{
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
example : progRejects (prog{
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
example : progRejects (prog{ fn Bad (b : &mut Nat) -> &mut Bool { b }; () })
  "owed type" = true := by native_decide

/-! ## The constrained branch, retired with its rule (M28 τ)

    A hand-built `constrained` group used to be handed to `endGroup` directly, to
    drive the one branch no call could reach: the identity wire, where a captured
    owner recovers the issued borrow's SURRENDERED payload instead of a fresh
    existential. It was kept so the branch was not dead-untested.

    The branch is gone, so there is nothing to test. Inferring that wire from a
    signature is unsound — `through` and `advance` share one and differ in exactly
    what it would claim, which is this file's own §6.1 headline — and the flag that
    forced it on existed only to validate the differential. That validation is now
    stated at the comparator (`S9Diff`), so the kernel no longer carries a case for
    a rule it does not have. -/

end Dllbc.Tests.S7Group
end
-- └── end of what was `S7Group.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S12Inst.lean` ──────────────────────────────────────────────
section
/-!
# §12 test suite — dependent call-site instantiation

The keystone (§5.3, stated since M6, implemented now): a call instantiates the
callee's telescope at the actuals. `processArgs` threads a substitution — for a
pure/owned argument the consumed value, for a borrow argument the actual borrow
(so a later `*b` in a type reflects to the payload snapshot just passed, §5.2) —
and reads the remaining parameter types, the return type, and the owed types at
those actuals. Nothing downstream (lemma application, spec-carrying calls, the
two recursive quicksort calls composing by transitivity) works without it.

Two supporting moves land here too: the return type is now pinned at entry (a
dependent return type may mention a parameter the body consumes, so it cannot be
re-read at return), and — the σ-refinement interaction — an instantiated return
or owed type may mention a caller σ, so it must refine when that σ does. The
"refinement reaches all σ-bearing state" invariant (built in M10 for
obligations) is extended to groups and the pinned return type; this milestone is
its first external consumer.

Plus the two mechanical dream-program clears: Term-level `Std` (so `Le`/`Sorted`
sit at telescope positions) and `if`-sugar over the Bool match.

**Written as programs** (M28 ν). A call cohort is a `fn` CHAIN — callee above
caller, which is what "a callee is a binding lexically above the call" means when
said in the grammar rather than assembled into a table. The shared callees
(`use_refl`, `needs`, `observe`) are written into each cohort that uses one
rather than factored into a prefix helper: a `%`-spliced tail may not declare
functions, because both chains number their slots from `progBase` and the inner
would shadow the outer, so a cohort whose members are all `fn`s has to be one
chain. The repetition is the honest cost of that, and it is four lines.
-/

open Dllbc
open Dllbc.Std (le_reflT)

namespace Dllbc.Tests.S12Inst

/-! ## The dependent return type, instantiated at the actual -/

-- `use_refl (n : Nat) → Le n n = LeRefl n`. The body ⇒-lifts the proof term
-- `LeRefl n` (pure lift, §11); the audit checks it against the pinned `Le n n`.
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

/-! ## A dependent second parameter (the M6 misresolution case, now correct) -/

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
def callNeeds3 : Term := prog{
  fn Needs (a : Nat, p : Le a 2) -> Unit { () };
  fn CallNeeds3 () -> Unit { Needs(3, ()) };
  () }
example : progRejects callNeeds3 "does not have its parameter type" = true := by
  native_decide

/-! ## A borrow-snapshot dependency (`*b`-in-types, exercised at a CALL) -/

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
def observeBad : Term := prog{
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

/-! ## `if`-sugar over the Bool match (dream-program gap 5) -/

-- `classify (b : Bool) → Nat = if b { 1 } else { 0 }` desugars to a fresh-var let
-- and a `match` on it; a symbolic `Bool` splits into two audited paths.
def classify : Term := prog{
  fn Classify (b : Bool) -> Nat { if b { 1 } else { 0 } };
  () }
example : progOk classify = true := by native_decide

/-! ## §12.7 The dream program, re-annotated

    Which M11 GAP[..] tags this milestone clears, and what remains.

    CLEARED by M12:
    * GAP[dependent call] — dependent call-site instantiation is in. Every
      spec-carrying call and lemma application now type-checks at its actuals;
      the two recursive quicksort calls can compose their `Sorted`/`Perm` specs
      by transitivity (once the transitivity lemma exists — see the OTHER wall).
    * GAP[Term-level Std] (gap 2) — `LeT`/`SortedT`/`countT`/`BoundT` sit at
      telescope, return, and owed positions now.
    * GAP[bool guard] / `if` (gap 5) — `if e { … } else { … }` is macro sugar
      over the Bool match; `Leb`/`Eqb` reflect to `Bool` and guard directly.

    STILL OPEN (the M13+ train, unchanged in priority order):
    * GAP[two-cursor swap / access-at-depth-i] — the naturalness make-or-break.
      Instantiation lets us STATE `swap`'s count-preservation spec; expressing
      the swap BODY (two reborrow cursors to depths i and j, cross-write) still
      has no depth-indexed idiom. This is the next milestone.
    * GAP[slice split: take/drop reborrows] — a prefix riding the length bound, a
      suffix as a depth-(k+1) reborrow. `Take`/`Drop` on list snapshots are a
      mechanical Std addition (for the SPECS); the reborrow OPERATIONS are not.
    * GAP[nested-induction lemmas] — `LeTrans` and `count_swap` are the proofs
      the specs above will consume. As raw eliminator terms they are impractical
      (the M11 LeTrans wall); this is the dependent-match-elaboration milestone,
      which instantiation (this milestone) is the precondition for.
    * ~~GAP[bounded recursion / decreasing [k]] — partial correctness is fine with
      signature-only recursion; the totality index (§8) is deferred.~~ **CLOSED
      (M26).** Signature-only recursion is gone: a `fn` elaborates to a sealed
      recursor, so a self-call is `ih` at a structurally smaller scrutinee and
      totality is a property of the form rather than a deferred side condition.
      `[k]` survives only as the hint for which argument that scrutinee is, and
      the elaboration is `fnElab` (M27).
-/

end Dllbc.Tests.S12Inst
end
-- └── end of what was `S12Inst.lean` ───────────────────────────────────────────────

-- ┌── was `Dllbc/Tests/S14Bounds.lean` ──────────────────────────────────────────────
section
/-!
# §14 test suite — bounds-proof cursors

The M13 swap worked but paid for out-of-bounds with a default-element parameter,
threaded through every call and every caller — the dominant contortion by the
naturalness memo's numbers. This milestone replaces it with the dependent option
(now expressible after M10–M12): a cursor carries a **bounds proof**, its
out-of-range branch is a ⊥-conflict discharge, and an out-of-bounds call is
rejected *at the call site* because no proof of the false bound exists.

The prerequisite — that borrow-mode symbolic match refines the payload snapshot,
so a parameter type mentioning `Len *v` computes per branch — was verified
standalone before building any of this (M3 refinement at the payload + the M10
"refinement reaches all σ-bearing state" invariant, confirmed by a probe whose
`Nil` branch discharges `Le (S i) 0 = ⊥` and whose negative controls fail).

Shape decision for `nth2`: `(pij : Le (S i) j, p2 : Le (S j) (Len *v))` with
`i < j` from `pij`. Chosen over `(p1 : Le (S i) (Len *v), p2 : …)` because it
needs no third proof and no `LeTrans`: `p2` discharges `Nil` (`Le (S j) 0 = ⊥`),
`pij` discharges the `j ≤ i` branches (`Le (S i) j = ⊥` there), the valid branch
needs no proof for the head element, and both proofs pass to the recursive call
*definitionally* (`Le (S(S k)) (S j') ≡ Le (S k) j'`). At concrete calls the
proofs are `()` (the ⊤ inhabitant); at symbolic calls they are parameters.
-/

open Dllbc

namespace Dllbc.Tests.S14Bounds

-- Expected concrete result Vals (test subjects).
def vnat : Nat → Val | 0 => .ctor "Z" [] | n + 1 => .ctor "S" [vnat n]
def vlist : List Nat → Val | [] => .ctor "Nil" [] | h :: t => .ctor "Cons" [vnat h, vlist t]

/-! ## The segment vocabulary computes (`Len`/`Take`/`Drop`) -/

example : (Val.nfV 1000 (Dllbc.Std.len (Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3])) == vnat 3) = true := by
  native_decide
example : (Val.nfV 1000 (Dllbc.Std.take (Std.ofNat 2) (Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]))
    == vlist [1, 2]) = true := by native_decide
example : (Val.nfV 1000 (Dllbc.Std.drop (Std.ofNat 2) (Dllbc.Std.ofList [Std.ofNat 1, Std.ofNat 2, Std.ofNat 3]))
    == vlist [3]) = true := by native_decide

/-! ## The cursor family, as a PREFIX

    `NthL`, `nth2` and `swap` are one chain: `nth2` calls `NthL`, `swap` calls `nth2`,
    and a callee is in scope by being written above its caller (§8). Every caller
    below rides the same chain as its tail, so what is checked and what is run is
    the function declared above the code that calls it — no table anywhere.

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
                 pij : Le (S i) j, p2 : Le (S j) (Len *v)) -> Σ (x : &mut Nat) → &mut Nat {
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
    let pr = Nth2(v, i, j, pij, p2);
    match pr { Pair(ei, ej) => {
      let t = *ei;
      *ei := *ej;
      *ej := t;
      () } } };
  %rest }

/-- All three check, as the one program they are. `nth2`'s call to `NthL` and
    `swap`'s to `nth2` are retargeted into the chain, which for `NthL`/`nth2` also
    exercises the `[i]` HOIST: the decreasing parameter is second, so a caller
    writing declaration order is permuted into the sealed telescope. -/
def cursors : Term := withCursors prog{ () }
example : progOk cursors = true := by native_decide

/-! ## Callers — concrete proofs are `()`, OOB is a call-site rejection -/

-- `swap(bb, 0, 2, (), ())`: `Le 1 2` and `Le 3 3` both whnf to ⊤, inhabited by `()`.
def swapBody : Term := withCursors prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  Swap(bb, 0, 2, (), ());
  let y = x;
  () }
example : progOk swapBody = true := by native_decide

-- CONCRETELY: `swap(v, 0, 2)` on `[1,2,3]` yields `[3,2,1]`.
example :
    (match Dllbc.Tests.S9Diff.runExec swapBody with
     | .ok env => env.lookup "y" == some (vlist [3, 2, 1])
     | .error _ => false) = true := by native_decide

-- OUT OF BOUNDS is rejected at the CALL SITE: `swap(bb, 0, 4, (), ())` needs
-- `p2 : Le (S 4) (Len [1,2,3]) = Le 5 3 = ⊥`, and `()` cannot inhabit ⊥.
def oobBody : Term := withCursors prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  Swap(bb, 0, 4, (), ());
  let y = x;
  () }
example : progRejects oobBody "does not have its parameter type" = true := by
  native_decide

/-! ## The multi-issued `endGroup` cascade, and a rejection (re-shaped from §13) -/

-- Both cursors live, then the owner is demanded: `endGroup` ends both issued
-- borrows in list order, then releases `v`.
def cascade : Term := withCursors prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  let pp = Nth2(bb, 0, 2, (), ());
  match pp { Pair(ei, ej) => { *ei := 9; *ej := 8; let y = x; () } } }
example : progOk cascade = true := by native_decide

-- Take a cursor's payload (hole) then demand the owner: the group cannot end.
def rejectProbe : Term := withCursors prog{
  let x = Cons(1, Cons(2, Cons(3, Nil)));
  let bb = &m x;
  let pp = Nth2(bb, 0, 2, (), ());
  match pp { Pair(ei, ej) => { let taken = *ei; let y = x; () } } }
example : progRejects rejectProbe "nothing surrendered" = true := by native_decide

/-! ## Differential coverage — bounds-proof pool, concrete proofs by computation -/

example : Dllbc.Tests.S9Diff.diffV2 swapBody = true := by native_decide

end Dllbc.Tests.S14Bounds
end
-- └── end of what was `S14Bounds.lean` ───────────────────────────────────────────────
