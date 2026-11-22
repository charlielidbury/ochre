import Ochr.Meaning.Steps.MasterGuards

/-!
# The hint sites: pins for the audit of docs/31 D172 (lead24, 2026-11-22)

The table of every sub-run of the reference's `runT`, with the hint each side hands down, is docs/31 D172. Pinned
here, every verdict by running the checker:

**The untyped tail out of tail position (main's D124, MERGED by machine9: the pins below FLIPPED).** Before the merge
the untyped `evalCore` handed a `let`'s tail, a `;`'s tail and both matches' arms the hint at every tail flag; the
typed run hands none (out of tail position), and so does the reference (`Run.tailHint`, D156); since D124 the untyped
run hands none there too. Smallest run: `let y = Z; N` with
`inductive L (A : Type) := N`, untyped, out of tail position, at the hint `L(Nat)`: the tail's bare `N` records the
hint's parameter (`N` at `[Nat]`) before D124; at no hint it records none; the typed run rejects it ("cannot
infer"). Since D124 the untyped run at the hint records `[]` too. The untyped steps state it as named checker facts,
one per site (`UntypedLetTailNoHint`, `UntypedSeqTailNoHint`, `UntypedMatchNatArmNoHint`,
`UntypedMatchIndArmNoHint`): TRUE since the merge, PROVED (`Machine.untypedLetTailNoHint` and its three siblings,
`Steps/Machine/HintFacts.lean`).

**`split` has no reference clause (finding).** `split f in u` and `split f { … }` (D61) are accepted in tail position;
`runT` has no clause for them (`.prim _ _ => SM.fail`), so the reference's run of every body ending in one fails
(`run_split_fails`) and `TailAt` is false there as the model stands. Accepted program: `PickNotZero` below.
-/

open Ochr.Test

ochr HintSplit {
  inductive B := T | F
  def IsZ (n : Nat) : B := match n { Z => T, S(m) => F }
  def Pick (n : Nat) : Nat := (let b = IsZ(n); match b { F => 1, T => 2 })
  def PickNotZero (n : Nat) : Eq(B, IsZ(Pick(n)), F) := split IsZ in refl
}

namespace Ochr.Meaning.Steps.Form.HintSites

open Ochr Ochr.Meaning Ochr.Meaning.Steps.Form
open Ochr.Meaning.Regress.GenNeutralContent (isOk outVal)

-- the checker accepts every definition, `split` included
#guard (Ochr.Test.runWith (some Prelude) "HintSplit" HintSplit {} (located := false)).allAsExpected

/-- `PickNotZero`'s body, resolved to the core: `split IsZ in refl` is the primitive `split` of the constant `IsZ`. -/
def pickBody : Option Term :=
  let p := Prelude.decls ++ HintSplit.decls
  match p.find? (·.name == "PickNotZero") with
  | some d => match (Ochr.Surface.runResolve p d 100000).1 with
    | .ok (.ok (.defn df)) => some df.body
    | _ => none
  | none => none

#guard match pickBody with
  | some (.prim "split" [.const "IsZ", _]) => true
  | _ => false

/-- **The reference runs `split f in u` as `u`** (docs/31 D175, the lead's ruling; it failed before, as
`run_split_fails`): at the form's own hint and tail flag, wherever the table does not erase the split. `PickNotZero`'s
body is of this shape. -/
theorem run_split (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (f : String) (u : Term)
    (s : SState) (hfl : K.D.flags (scopeOf s) (.prim "split" [.const f, u]) = (false, false)) :
    runT K ρ φ tl hint (.prim "split" [.const f, u]) s = runT K ρ φ tl hint u s := by
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.prim "split" [.const f, u])) (runT K ρ φ tl hint u) s = _
  rw [hfl]
  simp only [SM.erasedIf, SM.stmtIf]
  rfl

/-- The braces form has no clause yet (docs/31 D178: its core term binds `()` in place of the split value). -/
theorem run_splitArms_fails (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (f : String)
    (w : Term) (s : SState) : runT K ρ φ tl hint (.prim "splitArms" [.const f, w]) s = none := by
  rw [runT]
  all_goals first | rfl | (intros; simp_all)

/-! ## What the checker's UNTYPED run does with a `split` (lead25; docs/31 D175)

The lead ruled (task 2(a), lead25's brief) that the reference runs a `split`'s term, and asked first what the
checker's untyped run does. It does NOT run the term: `evalCore` rejects both forms at every tail flag, typed or
untyped ("split: only in tail position"); only `checkTail` handles them. A data-valued function whose body ends in a
split is accepted (`G`, `G2` below: the goal `V(IsZ(n))` is stuck on `IsZ(n)`), but a call of it is run by the
checker's untyped run of the body (`runBody`), which fails there: every caller is rejected (`H`, `H2`, `H3`). -/

ochr SplitData {
  inductive B := T | F
  def IsZ (n : Nat) : B := match n { Z => T, S(m) => F }
  def V (b : B) : Type := match b { T => Nat, F => Unit }
  def G (n : Nat) : V(IsZ(n)) := split IsZ { T => Z, F => () }
  def G2 (n : Nat) : V(IsZ(n)) := split IsZ in match IsZ(n) { T => Z, F => () }
  reject def H : Nat := G(Z)
  reject def H2 (n : Nat) : V(IsZ(n)) := G(n)
  reject def H3 : Unit := G(S(Z))
}

-- `G` and `G2` (data-valued, ending in a split) are accepted; every call of `G` that the checker runs is rejected
#guard (Ochr.Test.runWith (some Prelude) "SplitData" SplitData {} (located := false)).allAsExpected

/-- The checker's error, or `""`. -/
def errMsg {α : Type} (f : M α) (st : MState) (fuel : Nat) : String :=
  match (runMachine f st fuel).1 with
  | .fail (.error m _) => m
  | _ => ""

-- the untyped run of either form fails, with the tail-position error, at every tail flag
#guard errMsg (Ochr.eval 100 false (.prim "split" [.const "IsZ", .zero]) none) {} 1000 ==
  "split: only in tail position (where the goal is known)"
#guard errMsg (Ochr.eval 100 false (.prim "splitArms" [.const "IsZ", .letIn ⟨"h"⟩ .zero .zero]) none) {} 1000 ==
  "split: only in tail position (where the goal is known)"
#guard errMsg (Ochr.eval 100 false (.prim "split" [.const "IsZ", .zero]) none) { tailNext := true } 1000 ==
  "split: only in tail position (where the goal is known)"
#guard errMsg (Ochr.eval 100 false (.prim "splitArms" [.const "IsZ", .letIn ⟨"h"⟩ .zero .zero]) none) { tailNext := true } 1000 ==
  "split: only in tail position (where the goal is known)"

/-! ## The untyped tail (main's D124) -/

/-- `inductive L (A : Type) := N`, as a declaration. -/
def declL : IndDecl := { name := "L", params := [(⟨"A"⟩, .sort 1)], ctors := [("N", [])] }

/-- One frame, `L` declared; the tail flag clear (not in tail position). -/
def stL : MState := { env := #[{ binds := #[] }], inds := [declL] }

/-- `let y = Z; N`, `N` the bare constructor of `L`. -/
def tLetN : Term := .letIn ⟨"y"⟩ .zero (.ctor "L" 0 ⟨"N"⟩ [] [])

-- not in tail position
#guard stL.curTail == false && stL.tailNext == false
-- FLIPPED at main's D124 (merged by machine9): out of tail position the untyped run at the hint `L(Nat)` hands the
-- tail NO hint, and `N` records nothing, as at no hint (before the merge it recorded `Nat`)
#guard Value.exact (outVal (Ochr.eval 100 false tLetN (some (.tInd "L" [.tNat]))) stL 100000).1 (.ind "L" 0 ⟨"N"⟩ [] [])
#guard !Value.exact (outVal (Ochr.eval 100 false tLetN (some (.tInd "L" [.tNat]))) stL 100000).1 (.ind "L" 0 ⟨"N"⟩ [.tNat] [])
-- in tail position it hands the hint, as the typed check hands the goal
#guard Value.exact (outVal (Ochr.eval 100 false tLetN (some (.tInd "L" [.tNat]))) { stL with tailNext := true } 100000).1
  (.ind "L" 0 ⟨"N"⟩ [.tNat] [])
-- at no hint it records nothing
#guard Value.exact (outVal (Ochr.eval 100 false tLetN none) stL 100000).1 (.ind "L" 0 ⟨"N"⟩ [] [])
#guard !Value.exact (outVal (Ochr.eval 100 false tLetN none) stL 100000).1 (.ind "L" 0 ⟨"N"⟩ [.tNat] [])
-- the typed run hands the tail no hint: rejected
#guard !isOk (Ochr.eval 100 true tLetN (some (.tInd "L" [.tNat]))) stL 100000

/-- `Z; N`. -/
def tSeqN : Term := .seq .zero (.ctor "L" 0 ⟨"N"⟩ [] [])

/-- One frame, `L` declared, `x ↦ Z : Nat`, `y ↦ N[Nat] : L(Nat)`; not in tail position. -/
def bxZ : Binding := { hint := ⟨"x"⟩, ty := some .tNat, val := .zero, decl := .other }
def byN : Binding := { hint := ⟨"y"⟩, ty := some (.tInd "L" [.tNat]), val := .ind "L" 0 ⟨"N"⟩ [.tNat] [], decl := .ind "L" [.other] }
def stLx : MState := { env := #[{ binds := #[bxZ, byN] }], inds := [declL] }

/-- `match x { Z => N, S _ => N }`. -/
def tMatchNatN : Term := .matchNat (.var 1) (.ctor "L" 0 ⟨"N"⟩ [] []) (.ctor "L" 0 ⟨"N"⟩ [] [])

/-- `match y { N => N }`. -/
def tMatchIndN : Term := .matchInd (.var 0) "L" [(⟨"N"⟩, .ctor "L" 0 ⟨"N"⟩ [] [])]

/-- `N` recording `Nat`, and recording nothing. -/
def nNat : Value := .ind "L" 0 ⟨"N"⟩ [.tNat] []
def nNil : Value := .ind "L" 0 ⟨"N"⟩ [] []

#guard stLx.curTail == false && stLx.tailNext == false
-- FLIPPED at main's D124 (merged by machine9), each at its site: out of tail position the untyped run at the hint
-- `L(Nat)` hands the tail or arm NO hint (before the merge it handed it, and `N` recorded `Nat`)
-- (`Value.exact` reads the recorded parameters; `==` (`Value.beq`) ignores them; each pin is beside its negation)
#guard Value.exact (outVal (Ochr.eval 100 false tSeqN (some (.tInd "L" [.tNat]))) stL 100000).1 nNil
#guard !Value.exact (outVal (Ochr.eval 100 false tSeqN (some (.tInd "L" [.tNat]))) stL 100000).1 nNat
#guard Value.exact (outVal (Ochr.eval 100 false tMatchNatN (some (.tInd "L" [.tNat]))) stLx 100000).1 nNil
#guard !Value.exact (outVal (Ochr.eval 100 false tMatchNatN (some (.tInd "L" [.tNat]))) stLx 100000).1 nNat
#guard Value.exact (outVal (Ochr.eval 100 false tMatchIndN (some (.tInd "L" [.tNat]))) stLx 100000).1 nNil
#guard !Value.exact (outVal (Ochr.eval 100 false tMatchIndN (some (.tInd "L" [.tNat]))) stLx 100000).1 nNat
-- in tail position each hands the hint
#guard Value.exact (outVal (Ochr.eval 100 false tSeqN (some (.tInd "L" [.tNat]))) { stL with tailNext := true } 100000).1 nNat
#guard Value.exact (outVal (Ochr.eval 100 false tMatchNatN (some (.tInd "L" [.tNat]))) { stLx with tailNext := true } 100000).1 nNat
#guard Value.exact (outVal (Ochr.eval 100 false tMatchIndN (some (.tInd "L" [.tNat]))) { stLx with tailNext := true } 100000).1 nNat
-- at no hint each records nothing
#guard Value.exact (outVal (Ochr.eval 100 false tSeqN none) stL 100000).1 nNil
#guard !Value.exact (outVal (Ochr.eval 100 false tSeqN none) stL 100000).1 nNat
#guard Value.exact (outVal (Ochr.eval 100 false tMatchNatN none) stLx 100000).1 nNil
#guard !Value.exact (outVal (Ochr.eval 100 false tMatchNatN none) stLx 100000).1 nNat
#guard Value.exact (outVal (Ochr.eval 100 false tMatchIndN none) stLx 100000).1 nNil
#guard !Value.exact (outVal (Ochr.eval 100 false tMatchIndN none) stLx 100000).1 nNat

/-! The four sites of main's D124, ONE named fact each (the lead's ruling (b), lead25's brief: kept separate so
each is discharged when its change lands). Each was FALSE before the merge (the pins above, flipped; `tLetN` for the
`let`) and is PROVED since (`Steps/Machine/HintFacts.lean`): out of tail position (`curTail = false`) the untyped
`evalCore` of the former at any hint runs exactly as at no hint. In tail position the untyped run, the typed check
and the reference all hand the hint. -/

/-- **D124 at a `let`'s tail** (pin `tLetN`; PROVED, `Machine.untypedLetTailNoHint`). -/
def UntypedLetTailNoHint : Prop :=
  ∀ (n : Nat) (x : Hint) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (r : Value × Option Value),
    st.curTail = false →
    (Runs (Ochr.evalCore (n + 1) false (.letIn x u w) hint) st bh r st' ↔
      Runs (Ochr.evalCore (n + 1) false (.letIn x u w) none) st bh r st')

/-- **D124 at a `;`'s tail** (pin `tSeqN`; PROVED, `Machine.untypedSeqTailNoHint`). -/
def UntypedSeqTailNoHint : Prop :=
  ∀ (n : Nat) (u w : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (r : Value × Option Value),
    st.curTail = false →
    (Runs (Ochr.evalCore (n + 1) false (.seq u w) hint) st bh r st' ↔
      Runs (Ochr.evalCore (n + 1) false (.seq u w) none) st bh r st')

/-- **D124 at a match on a number's arms** (pin `tMatchNatN`; PROVED, `Machine.untypedMatchNatArmNoHint`). -/
def UntypedMatchNatArmNoHint : Prop :=
  ∀ (n : Nat) (p : Place) (z u : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (r : Value × Option Value),
    st.curTail = false →
    (Runs (Ochr.evalCore (n + 1) false (.matchNat p z u) hint) st bh r st' ↔
      Runs (Ochr.evalCore (n + 1) false (.matchNat p z u) none) st bh r st')

/-- **D124 at a match on a declared inductive's arms** (pin `tMatchIndN`; PROVED, `Machine.untypedMatchIndArmNoHint`). -/
def UntypedMatchIndArmNoHint : Prop :=
  ∀ (n : Nat) (p : Place) (ty : String) (arms : List (Hint × Term)) (hint : Option Value) (st st' : MState) (bh : Nat)
    (r : Value × Option Value),
    st.curTail = false →
    (Runs (Ochr.evalCore (n + 1) false (.matchInd p ty arms) hint) st bh r st' ↔
      Runs (Ochr.evalCore (n + 1) false (.matchInd p ty arms) none) st bh r st')

/-! ## `J`'s transported term: the typed check's two paths (the lead's (c); docs/31 D175)

Where `J` computes the typed check runs `t` with no hint; where it is stuck the block's arm runs `t` at `P(a)`. Pinned
on a bare constructor of a declaration with a parameter: `JL` (stuck) is accepted because the arm hands `P(a)`, `JL2`
(computing) is rejected for want of the parameter. The checker lane is making the two paths agree; this pin flips
then, whichever hint they agree on. -/

ochr JHint {
  inductive L (A : Type) := N | C(h : A, t : L(A))
  def JL (a : Nat) (b : Nat) (h : Eq(Nat, a, b)) : L(Nat) := J(Nat, a, b, λ(z : Nat) : Type => L(Nat), h, N)
  reject def JL2 : L(Nat) := J(Nat, 0, 0, λ(z : Nat) : Type => L(Nat), refl, N)
  def JL3 : L(Nat) := J(Nat, 0, 0, λ(z : Nat) : Type => L(Nat), refl, N[Nat])
}

-- TODAY: the stuck path hands `P(a)` (JL accepted), the computing path none (JL2 rejected)
#guard (Ochr.Test.runWith (some Prelude) "JHint" JHint {} (located := false)).allAsExpected

/-! ## `clone`/`peek` of a place (the lead's (e); main's D122, merged into this line by machine9) -/

/-- **`clone` and `peek` take a place** (a fact about the checker; FALSE on this line's checker before the merge of
main's D122, PROVED since: `Machine.clonePeekPlace`, `Steps/Machine/HintFacts.lean`): every successful `evalCore` of
`clone(u)` or `peek(u)` has a place operand. Pin, FLIPPED at the merge: `MasterGuards`' `checkDef defCL`
(`let x = S(Z); let y = clone(S(x)); x`, accepted before, rejected since). -/
def ClonePeekPlace : Prop :=
  ∀ (n : Nat) (typed : Bool) (f : String) (u : Term) (hint : Option Value) (st st' : MState) (bh : Nat)
    (r : Value × Option Value),
    (f = "clone" ∨ f = "peek") → Runs (Ochr.evalCore (n + 1) typed (.prim f [u]) hint) st bh r st' →
    ∃ p, u = .place p

end Ochr.Meaning.Steps.Form.HintSites
