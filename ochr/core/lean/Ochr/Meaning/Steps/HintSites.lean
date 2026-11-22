import Ochr.Meaning.Steps.MasterGuards

/-!
# The hint sites: pins for the audit of docs/31 D172 (lead24, 2026-11-22)

The table of every sub-run of the reference's `runT`, with the hint each side hands down, is docs/31 D172. Pinned
here, every verdict by running the checker:

**The untyped tail out of tail position (main's D124, ruled (1): to land, then this pin FLIPS).** Today the untyped
`evalCore` hands a `let`'s tail, a `;`'s tail and both matches' arms the hint at every tail flag; the typed run hands
none (out of tail position), and so does the reference (`Run.tailHint`, D156). Smallest run: `let y = Z; N` with
`inductive L (A : Type) := N`, untyped, out of tail position, at the hint `L(Nat)`: the tail's bare `N` records the
hint's parameter (`N` at `[Nat]`); at no hint it records none; the typed run rejects it ("cannot infer"). After
main's D124 the untyped run at the hint records `[]` too. `UntypedTailNoHint` is the named checker fact the untyped
steps state against it: FALSE today (`untyped_tail_reads_hint` below), true after D124.

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

/-- **The reference fails on `split`**: `runT` has no clause for it. -/
theorem run_split_fails (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (f : String) (u : Term)
    (s : SState) : runT K ρ φ tl hint (.prim "split" [.const f, u]) s = none := by
  rw [runT]
  all_goals first | rfl | (intros; simp_all)

/-! ## The untyped tail (main's D124) -/

/-- `inductive L (A : Type) := N`, as a declaration. -/
def declL : IndDecl := { name := "L", params := [(⟨"A"⟩, .sort 1)], ctors := [("N", [])] }

/-- One frame, `L` declared; the tail flag clear (not in tail position). -/
def stL : MState := { env := #[{ binds := #[] }], inds := [declL] }

/-- `let y = Z; N`, `N` the bare constructor of `L`. -/
def tLetN : Term := .letIn ⟨"y"⟩ .zero (.ctor "L" 0 ⟨"N"⟩ [] [])

-- not in tail position
#guard stL.curTail == false && stL.tailNext == false
-- TODAY (flips after main's D124): the untyped run at the hint `L(Nat)` hands the tail the hint, and `N` records `Nat`
#guard (outVal (Ochr.eval 100 false tLetN (some (.tInd "L" [.tNat]))) stL 100000).1 == .ind "L" 0 ⟨"N"⟩ [.tNat] []
-- at no hint it records nothing
#guard (outVal (Ochr.eval 100 false tLetN none) stL 100000).1 == .ind "L" 0 ⟨"N"⟩ [] []
-- the typed run hands the tail no hint: rejected
#guard !isOk (Ochr.eval 100 true tLetN (some (.tInd "L" [.tNat]))) stL 100000

/-- **Out of tail position, an untyped `let`, `;` or match hands its tail or arm no hint** (a fact about the
checker; FALSE today, true after main's D124, ruled (1)): from a state not in tail position (`curTail = false`), the
untyped `evalCore` of a `let`, a `;` or either match at any hint runs exactly as at no hint. The untyped steps for
these four formers state it, counted, as `clone`/`peek` state main's D122. -/
def UntypedTailNoHint : Prop :=
  ∀ (n : Nat) (t : Term) (hint : Option Value) (st st' : MState) (bh : Nat) (r : Value × Option Value),
    (∃ x u w, t = .letIn x u w) ∨ (∃ u w, t = .seq u w) ∨ (∃ p z u, t = .matchNat p z u) ∨
      (∃ p ty arms, t = .matchInd p ty arms) →
    st.curTail = false →
    (Runs (Ochr.evalCore (n + 1) false t hint) st bh r st' ↔ Runs (Ochr.evalCore (n + 1) false t none) st bh r st')

end Ochr.Meaning.Steps.Form.HintSites
