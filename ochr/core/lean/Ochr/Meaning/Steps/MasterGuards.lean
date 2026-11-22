import Ochr.Meaning.Steps.RecGuards

/-!
# Guards for the master induction's findings (lead22, 2026-11-22; docs/31 D150)

Every `#guard` runs the checker.

**`clone` of a term that is not a place** (FIXED by main's D122, merged into this line by machine9: the core checker
now rejects `clone` and `peek` of anything but a place; the pin below flipped). The surface produces `clone` only of a
place (`Surface.lean`: "clone takes a place"), but the core checker accepted `clone(u)` for every `u`: it ran `u` in copying
mode (`withCopying`), where every read of a place leaves it in place. The reference's `clone` clause
reads a place operand in place too, but runs any other operand by its plain run (`runT false hint u`),
whose read of a number variable MOVES it (the table's copy decision of a `let`-bound number is `.other`'s,
never a copy). So for `let x = S(Z); let y = clone(S(x)); x` the checker accepts and the reference's
strict run fails at the last read (`x` moved): the general `prim` step is false for `clone` of a
non-place unless the core checker rejects it or the reference copies inside it.
-/

open Ochr.Test

/- A bare constructor of a declaration with a parameter, as the tail of a `let` ending a function's body: the
typed checker in tail position (`checkTailAt`'s `.letIn` case, then its default case) evaluates the tail with
the GOAL as its hint, which gives the constructor its parameter; the reference's `.letIn` clause ran its tail
with no hint (`.plain TyM.err`), and a bare constructor of a declaration with parameters and no record fails
(`runT`'s `.ctor` clause). FIXED by docs/31 D156 (in tail position the reference hands the tail its hint,
`Run.tailHint`); the regression on both sides is `Steps/TailHintRegress.lean`. Accepted (the block elaborates only if the checker accepts every definition: a rejected one is an elaboration error,
checked on `def H : L(Nat) := let x = Z; N`, a constant, whose body `eval` runs, rejected for want of the
parameter). The same for a match's arms (`F2`) and a sequence's tail (`F3`). -/

ochr MasterProbeTailHint {
  inductive L (A : Type) := N | C(h : A, t : L(A))
  def F (n : Nat) : L(Nat) := let x = n; N
  def G (n : Nat) : L(Nat) := N
  def F2 (n : Nat) : L(Nat) := match n { Z => N, S(m) => N }
  def F3 (n : Nat) : L(Nat) := (n; N)
}

/- **What the erased depth gates** (ruling (b) of docs/31 D150; D155). The checker reads `erasedDepth` in exactly
three places (`Machine.lean`): `atRuntime` (K2's `unsizedCheck`; K3's `abstractMatchCheck` and the constructor of
an abstract type in `evalCore`'s `evalCtor`), `readPlace`'s capture-move check and `capture`'s; each rejects at
depth `0` only. The smallest programs the checker accepts only above depth `0`, each beside its twin at depth `0`
(rejected by that check and nothing else): a function returning a type runs its body one depth down
(`withErasedIf` in `checkFix`), so its body is an erased position. -/

ochr DepthProbe {
  -- D53: a closure's body moves a captured value out
  reject def Cap0 (n : Nat) : Nat := ((λ(m : Nat) : Nat => n); Z)
  def CapE (n : Nat) : Type := ((λ(m : Nat) : Nat => n); Nat)
  -- D53: a closure captures, by move, a captured value
  reject def Nest0 (n : Nat) : Nat := ((λ(m : Nat) : Nat => ((λ(k : Nat) : Nat => clone(n)); Z)); Z)
  def NestE (n : Nat) : Type := ((λ(m : Nat) : Nat => ((λ(k : Nat) : Nat => clone(n)); Z)); Nat)
  -- K3: a constructor of an abstract type
  abstract inductive A := MkA(k : Nat)
  reject def Ctor0 (n : Nat) : Nat := (MkA(n); Z)
  def CtorE (n : Nat) : Type := (MkA(n); Nat)
  -- K3: a match with the constructors of an abstract type
  reject def Match0 (a : &A) : Nat := match *a { MkA(k) => clone(k) }
  def MatchE (a : &A) : Type := match *a { MkA(k) => Nat }
  -- K2: a read of a place of an unsized type
  unsized abstract inductive V := MkV(k : Nat)
  reject def Read0 (v : &V) : Nat := (clone(*v); Z)
  def ReadE (v : &V) : Type := (clone(*v); Nat)
}

namespace Ochr.Meaning.Steps.Form.MasterGuards

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

/-- `let x = S(Z); let y = clone(S(x)); x` in the core (de Bruijn: `x` is `#0`, then `#1`). -/
def bodyCL : Term :=
  .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "clone" [.succ (.place (.var 0))]) (.place (.var 1)))

def defCL : Def := { name := "CL", hs := [], doms := [], cod := .nat, dec := none, body := bodyCL }

-- main's D122 (merged by machine9, spine-machine10): the core checker REJECTS it, "clone takes a place"; before the
-- merge it accepted it (`S(x)` under `clone` copied `x`), which was this finding. `HintSites.ClonePeekPlace` is now true
#guard !isOk (checkDef defCL) {} 100000

/-- The same without `clone`. -/
def bodyNC : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.succ (.place (.var 0))) (.place (.var 1)))

/-- `clone` of the place `x` itself. -/
def bodyCP : Term := .letIn ⟨"x"⟩ (.succ .zero) (.letIn ⟨"y"⟩ (.prim "clone" [.place (.var 0)]) (.place (.var 1)))

-- without `clone` the read of `x` in `S(x)` moves it, and the last read is rejected
#guard !isOk (checkDef { defCL with body := bodyNC }) {} 100000

-- `clone(x)` of the place itself is accepted (the case the reference reads in place)
#guard isOk (checkDef { defCL with body := bodyCP }) {} 100000

/-! ## Why `EvalAt` asks for the plain mode (docs/31 D150, D154)

`Form.lean`'s deleted `eval_sim` quantified over every mode. Inside `clone(x)` (`let x = S(Z); let y = clone(x); x`)
the checker reads `x` in copying mode and leaves it; the reference's plain run of the read moves it, and the
states after are not related. -/

/-- One frame, `x ↦ 1`, read `.other` at `Nat`. -/
def stX : MState := { env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some .tNat, val := .succ .zero, decl := .other }] }] }

open Ochr.Meaning.Regress.GenNeutralContent (outSt) in
-- in copying mode the read of `x` succeeds and leaves `x`; in the plain mode it moves `x`
#guard isOk (Ochr.eval 100 true (.place (.var 0)) none) { stX with copying := true } 100000 &&
  (outSt (Ochr.eval 100 true (.place (.var 0)) none) { stX with copying := true } 100000).env[0]!.binds[0]!.val ==
    .succ .zero
open Ochr.Meaning.Regress.GenNeutralContent (outSt) in
#guard isOk (Ochr.eval 100 true (.place (.var 0)) none) stX 100000 &&
  (outSt (Ochr.eval 100 true (.place (.var 0)) none) stX 100000).env[0]!.binds[0]!.val == .bot

/-! ## What the erased depth gates (D155) -/

/-- The checker's verdict on one definition of `DepthProbe`: `""` if accepted, else the message. -/
def depthVerdict (nm : String) : String :=
  match ((Ochr.Test.runWith none "DepthProbe" DepthProbe {} (located := false)).rows.find? (·.name == nm)) with
  | some r => match r.verdict with
    | Ochr.Verdict.accepted => ""
    | Ochr.Verdict.rejected m _ => m
    | Ochr.Verdict.undecided _ => "?"
  | none => "?"

-- every definition as marked: each `…E` accepted, each `…0` rejected
#guard (Ochr.Test.runWith none "DepthProbe" DepthProbe {} (located := false)).allAsExpected
-- each twin at depth `0` is rejected by the depth-gated check and nothing else
#guard (depthVerdict "Cap0").startsWith "[D53] a closure's body moves a captured value out"
#guard (depthVerdict "Nest0").startsWith "[D53] a closure's body moves a captured value (κ) into a closure"
#guard (depthVerdict "Ctor0").startsWith "[K3] the constructor MkA of the abstract type A at runtime"
#guard (depthVerdict "Match0").startsWith "[K3] a match on *a with the constructors of the abstract type A at runtime"
#guard (depthVerdict "Read0").startsWith "[K2] *v, of the unsized type V, is cloned at runtime"

end Ochr.Meaning.Steps.Form.MasterGuards
