import Dllbc.CompileCmd
import Dllbc.ProgMacro
import Dllbc.Tests.Diff

/-!
# M35 probe — the compiler, measured

**Not part of the default build.** `Dllbc.lean` does not import this file, so
nothing here can slow or redden `lake build Dllbc`.

Three things are asserted, in this order:

  1. **Coverage** — how much of the executing corpus is borrow-free, by name and
     by count. This is the honest denominator: the compiler's domain is the
     fragment with no loan in it, and the differential's own corpus is mostly
     *not* in that fragment, by design.
  2. **The differential** — for every borrow-free program here, the compiled Lean
     value equals the `Val` the DLLBC executing machine left in that slot. Both
     sides are computed and compared by `native_decide`; nothing is asserted by
     inspection.
  3. **Erasure** — programs that carry proofs and specs alongside their data, and
     the compiled output that has neither.
-/

open Dllbc Dllbc.Compile

namespace Dllbc.Tests.M35Compile

/-! ## §1. Coverage: what fraction of the executing corpus is borrow-free

    `S8Diff` generates 136 bodies across three telescopes and runs the accepted
    ones against a pool of concrete arguments — 238 concrete runs, the largest
    block of execution in the suite. Exactly one of the three telescopes is
    borrow-free, and the split is total rather than partial: a telescope
    containing `&mut` puts a `borrowT` in every program built from it, whatever
    the body does. -/

open Dllbc.Tests.S8Diff

/-- The `(v : &mut List Nat) → Unit` pool: NONE of it is borrow-free. -/
example : (vBodies.map vCheck).countP borrowFree = 0 := by native_decide

/-- The `(b : &mut Nat, c : Bool) → Unit` pool: none of it either. -/
example : (bcBodies.map bcCheck).countP borrowFree = 0 := by native_decide

/-- The `(n : Nat) → Nat` pool: ALL of it, generated and accepted alike. -/
example : (nBodies.map nCheck).countP borrowFree = 32 := by native_decide
example : (nAccepted.map nCheck).countP borrowFree = 15 := by native_decide

/-! ## §2. The differential over that pool

    `S8Diff.nRun` ends its program with `()`, which makes the answer invisible to
    anything but Ω. This is the same program with the answer in the tail, so that
    the compiled side has something to BE. Both sides still see the same `fn`,
    the same body, the same argument. -/

def nRunT (body arg : Term) : Term := prog{
  fn F (n : Nat) -> Nat { %body };
  let r = F(%arg);
  r }

/-- The 15 accepted bodies against the 3-element argument pool: 45 programs. -/
def pool45 : List Term := nAccepted.flatMap (fun b => nArgs.map (fun a => nRunT b a))

example : pool45.length = 45 := by native_decide
example : pool45.all borrowFree = true := by native_decide

-- All 45 compile, and this is where a compilation failure would surface.
example : pool45.all (fun t => (compileProgram t).toOption.isSome) = true := by native_decide

-- …and here they are, as 45 real Lean definitions.
compile_dllbc_each Pool45 from pool45

/-- **THE DIFFERENTIAL.** For each of the 45: the DLLBC executing machine ran the
    program and left a `Val` in slot `r`; the Lean function compiled from the same
    program computed a `Nat`. They are the same value. -/
example : (pool45.zip Pool45.all).all (fun p => agreesAt p.1 "r" p.2) = true := by
  native_decide

-- The differential is not vacuous: 45 comparisons really happened.
example : (pool45.zip Pool45.all).length = 45 := by native_decide

/-! ## §3. The standard library, compiled

    `Std.lean` is the verification vocabulary — `len`, `count`, `add`, `take`,
    `drop`, `eqb`, `leb` — written as raw recursor spines inside the calculus.
    Every one of them is in the borrow-free fragment, and every one of them
    compiles: `count` in particular is a `listRec` whose arm contains a `boolRec`
    whose scrutinee is an `eqb` spine (itself a double `natRec`), and it comes out
    as ordinary Lean code that runs. -/

def stdProg : Term := prog{
  let l = Cons(3, Cons(1, Cons(2, Cons(1, Nil))));
  let n = Len l;
  let c = Count 1 l;
  let s = Add n c;
  let t2 = Take 2 l;
  let d = Drop 2 l;
  let e = Eqb 1 1;
  let b = Leb 3 1;
  s }

example : borrowFree stdProg = true := by native_decide
example : progOk stdProg (.const "Nat") = true := by native_decide

compile_dllbc Std7 from stdProg

/-- Every slot the DLLBC machine left, against the Lean definition compiled from
    the same binding. Eight slots, four target types. -/
example :
  agreesAt stdProg "l" Std7.l && agreesAt stdProg "n" Std7.n
  && agreesAt stdProg "c" Std7.c && agreesAt stdProg "s" Std7.s
  && agreesAt stdProg "t2" Std7.t2 && agreesAt stdProg "d" Std7.d
  && agreesAt stdProg "e" Std7.e && agreesAt stdProg "b" Std7.b = true := by
  native_decide

-- …and the values are the ones a reader would predict, so a differential that
-- agreed because both sides were stuck would be visible here.
example : (Std7.n, Std7.c, Std7.s, Std7.e, Std7.b) = (4, 2, 6, true, false) := by native_decide
example : (Std7.t2, Std7.d) = ([3, 1], [2, 1]) := by native_decide

/-! ## §4. Erasure, as programs

    Three shapes, one rule. A **proof parameter** disappears from the signature
    and from every call; a **type or proof binding** never reaches the output; a
    **Σ carrying a postcondition** compiles to its data component alone. -/

/-- A function with a proof parameter, a type binding, a proof binding, and a
    call that supplies the proof. -/
def erasureProg : Term := prog{
  fn Idx (n : Nat, H : Le n n) -> Nat { n };
  let T = Nat;
  let p = %(Term.app Std.le_reflT (Std.ofNat 3));
  let r = Idx(3, p);
  r }

example : progOk erasureProg (.const "Nat") = true := by native_decide
example : borrowFree erasureProg = true := by native_decide

compile_dllbc Er from erasureProg

/-- `Idx` kept its `Nat` and lost its proof: the compiled type is `Nat → Nat`,
    not `Nat → Le n n → Nat`. Asserted as an APPLICATION, because that is the
    half a type ascription alone would not pin. -/
example : Er.Idx 3 = 3 := by native_decide
example : agreesAt erasureProg "r" Er.r = true := by native_decide

/-- The dropped bindings really are dropped: DLLBC's Ω has four entries here and
    the compiled namespace has two definitions. `T` (a type) and `p` (a proof)
    are the two that go. -/
example : (match runProgram erasureProg with
           | .ok env => env.map Prod.fst | .error _ => []) = ["Idx", "T", "p", "r"] := by
  native_decide
example : (match compileProgram erasureProg with
           | .ok cp => cp.defs.map CDef.name | .error _ => []) = ["Idx", "r"] := by
  native_decide

/-- A Σ carrying a postcondition compiles to its data component. -/
def sigProg : Term := prog{
  let q = (Pair(3, %(Term.app Std.le_reflT (Std.ofNat 3))) : Σ (X : Nat) → Le X X);
  q }

example : (match compileProgram sigProg with
           | .ok cp => cp.mainTy == CTy.nat | .error _ => false) = true := by native_decide

/-! ### §4b. Capital does NOT mean erasable — the claim, and its counterexample

    The expectation this probe was dispatched with is that erasure reads off the
    binder: capital is comptime, comptime is erased. `Std.addFn` is the standing
    refutation. Both of its binders are capital — `Var.isComptime` says so below —
    and it is the addition every program in the corpus computes with, so erasing
    either one turns `add 2 3` into a constant.

    What capitalisation controls is how the argument is READ (⇝-snapshot rather
    than ⇒-move), which is a question about ownership, not about relevance. The
    two questions were never the same one; the mode discipline answers the first
    and the TYPE answers the second. -/

/-- Both of `add`'s binders are comptime… -/
example : ((Term.peelLams Std.addFnT).1.map (fun p => p.1.isComptime)) = [true, true] := by
  native_decide

def addProg : Term := prog{
  let f = (%Std.addFnT : Π (A : Nat) → Π (B : Nat) → Nat);
  let r = f 2 3;
  r }

compile_dllbc AddP from addProg

/-- …and neither is erased: the compiled function is a genuine `Nat → Nat → Nat`
    that answers `5`, not a constant. -/
example : AddP.f 2 3 = 5 := by native_decide
example : agreesAt addProg "r" AddP.r = true := by native_decide

/-! ## §5. **Erasure is not stable under conversion** — the finding, asserted

    This is the sharpest thing the probe found, and it is a fact about the
    CALCULUS rather than about this compiler. DLLBC is type-in-type with no
    `Prop`, no proof irrelevance, and no irrelevance marker; its ⊤ is literally
    `Unit` and its ⊥ is `Bot`. So a spec and a datatype are not two kinds of
    thing — a spec REDUCES to one.

      * `Le 1 2` as a programmer writes it is an application spine with no case
        in `compileTy`, so it erases.
      * `Le 1 2` normalized is `Unit`, and `Unit` is data. It does not erase.
      * `Sorted [1,2]` normalized is `Σ Unit (Σ Unit Unit)` — a nested PAIR of
        units, which compiles to a nested `Prod` the compiled program builds and
        carries at runtime.

    …and the asymmetry that makes it more than an inconvenience: `Le 2 1`
    normalizes to `Bot`, which has no constructor and therefore erases. **Whether
    a proposition erases depends on whether it is TRUE.**

    Consequence for a real compilation story: erasure must be decided on the type
    as WRITTEN (which is what this compiler does — its only type reduction is β at
    the head, never `Pure.nf`), or the calculus needs an irrelevance marker. A
    compiler that normalized types first would silently keep proofs as data, and
    the two decisions would disagree exactly on the propositions that hold. -/

section ConversionStability
open Dllbc.Std

/-- As written: erased. Normalized: `Unit`, which is data. -/
example : compileTy (LeT (ofNat 1) (ofNat 2)) = CTy.erased := by native_decide
example : compileTy (Pure.nf 1000 (LeT (ofNat 1) (ofNat 2))) = CTy.unit := by native_decide

/-- A FALSE order fact normalizes to `Bot` and erases — so erasure tracks the
    truth of the proposition, not its kind. -/
example : compileTy (Pure.nf 1000 (LeT (ofNat 2) (ofNat 1))) = CTy.erased := by
  native_decide

/-- `Sorted` is worse than `Le`, because its normal form has STRUCTURE: a
    two-element sorted list's proof becomes a pair of pairs of units. -/
example : compileTy (SortedT (ofList [ofNat 1, ofNat 2])) = CTy.erased := by native_decide
example : compileTy (Pure.nf 1000 (SortedT (ofList [ofNat 1, ofNat 2])))
            = CTy.prod CTy.unit (CTy.prod CTy.unit CTy.unit) := by native_decide

end ConversionStability

/-! ## §6. The wall, named form by form

    The compiler refuses each borrow-fragment form by name rather than failing
    somewhere downstream, which is what makes the wall map below a map and not a
    guess. These five are §0's ownership machinery and ¶2.1's array steps — the
    exact complement of `borrowFree`. -/

def borrowProg : Term := prog{ let x = 3; let b = &m x; () }
def derefProg : Term := prog{ fn F (v : &mut List Nat) -> Unit { let t = *v; () }; () }
def assignProg : Term := prog{ fn F (v : &mut Nat) -> Unit { *v := 3; () }; () }

def refusal (t : Term) : String :=
  match compileProgram t with | .ok _ => "COMPILED" | .error e => e

example : refusal borrowProg = "BORROW (&m) — outside the borrow-free fragment" := by
  native_decide
example : refusal derefProg = "DEREF (*) — outside the borrow-free fragment" := by
  native_decide
example : refusal assignProg = "ASSIGN (:=) — outside the borrow-free fragment" := by
  native_decide

-- The three are outside `borrowFree` too, so the predicate and the compiler
-- agree about where the fragment ends.
example : [borrowProg, derefProg, assignProg].all (fun t => !borrowFree t) = true := by
  native_decide

/-! ## §7. `S9Diff`'s four callers — the borrow half of the corpus, measured

    The whole-program differential runs four callers over a four-function pool.
    None of them is borrow-free, and that is the shape of the corpus rather than
    an accident of these four: the pool's every function takes a `&mut`. -/

example : Dllbc.Tests.S9Diff.callers.countP borrowFree = 0 := by native_decide
example : Dllbc.Tests.S9Diff.callers.length = 4 := by native_decide

end Dllbc.Tests.M35Compile
