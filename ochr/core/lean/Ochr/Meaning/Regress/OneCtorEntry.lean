import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# A read of one field keeps a borrow of another live (D93; built)

The fourth concrete check (fifth lead, 2026-11-21, docs/31 D38). Main's D93: a match on a value of
a type with one constructor (a projection `x.i`, D81) never closes off, and has no entry (D90's
rule 2) and no join, on any path. So `let r = &x.1; let y = clone(x.0); *r := Z` is accepted, on a
known pair (`KP`) and on a parameter (`PP`, whose `x` the borrow `&x.1` already refined in place to
`(σ1, σ2)`). The reference always read a field directly; this checks that it now agrees.

At the checker's own state before `clone(x.0)` (recorded at a hole, `Config.recordStates`):
`x ↦ (σ, loan_0)`, `r ↦ borrow_0 σ'`, and `0`'s one site is `x` at the path `.field ⟨Pair, 0, 1⟩`.
- The checker's evaluation of `clone(x.0)` (the projection's one-arm match: [Access] of `x` for the
  tag, then the arm's read of `x.0`, with no entry) leaves `0` live, held by `r`, with the same site
  (`#guard`, both programs).
- The reference's read of `x.0` (`readPlace`'s access of `x` at `[.proj 0]`) on the related state
  leaves `0` live, held by `r`, with the same site (`ref_read_keeps`, kernel-checked). So the
  relation's holders and sites clauses hold afterwards with the identity renaming; the meanings
  are not computable.
- Before D93 the checker's entry read `x` whole, which the reference's access of `x` does too: it
  ends `0` (`ref_whole_ends`), the behaviour the reference no longer has to imitate.
-/

open Ochr.Test

ochr OneCtorEntry uses Nats {
  def KP (a : Nat) (b : Nat) : Unit := (let x = (a, b); let r = &x.1; let y = clone(x.0); *r := Z; ())
  def PP (x : Nat × Nat) : Unit := (let r = &x.1; let y = clone(x.0); *r := Z; ())
}

#guard_msgs (drop warning) in
ochr OneCtorEntryAt uses Nats {
  def KPAt (a : Nat) (b : Nat) : Unit := (let x = (a, b); let r = &x.1; ?)
  def PPAt (x : Nat × Nat) : Unit := (let r = &x.1; ?)
}

namespace Ochr.Meaning.Regress.OneCtorEntry
open Ochr Ochr.Meaning

/-- The checker's whole state at the hole of `name`, on entry. -/
def stAt (name : String) : MState :=
  let r := Ochr.Test.runWith (some Prelude) "OneCtorEntryAt" OneCtorEntryAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- `0`'s one site: field `1` of the pair. -/
def site1 (x : Pos) : Site := ⟨x, [.field ⟨"Pair", 0, 1, ""⟩], false⟩

def siteForm (x : Site) : Pos × List (Option (Nat × Nat)) × Bool := (x.pos, pathKey x.path, x.fill)

/-- The checker's `clone(x.0)` (`x` is variable `1`, `r` variable `0`). -/
def cloneX0 (fuel : Nat) : M Unit := discard (eval fuel true (.prim "clone" [.place (.proj 0 (.var 1))]))

def after (x : M Unit) (st : MState) (fuel : Nat) : Option MState :=
  match (runMachine x st fuel).1 with
  | .ok () st' => some st'
  | _ => none

/-- The checker keeps `0` live across the read, held by `r`, lent at field `1` of `x`. -/
def keeps (st : MState) (xPos rPos : Pos) : Bool :=
  match after (cloneX0 100000) st 1000000 with
  | some st' => liveLoan st'.env 0 && Env.shape st'.env rPos == some 0 &&
      (Env.sitesOf st'.env 0).map siteForm == [siteForm (site1 xPos)]
  | none => false

section KP
def stK : MState := stAt "KPAt"
-- `a`, `b`, `x`, `r` at positions 1–4 of frame 1; `0` held by `r`, lent at `x`'s field `1`
#guard (stK.env[1]!).binds.size == 5 && Env.shape stK.env (.bind 1 4) == some 0
#guard (Env.sitesOf stK.env 0).map siteForm == [siteForm (site1 (.bind 1 3))]
#guard keeps stK (.bind 1 3) (.bind 1 4)
end KP

section PP
def stP : MState := stAt "PPAt"
-- `x`, `r` at positions 1–2 of frame 1 (`x` refined in place by the borrow, D93)
#guard (stP.env[1]!).binds.size == 3 && Env.shape stP.env (.bind 1 2) == some 0
#guard (Env.sitesOf stP.env 0).map siteForm == [siteForm (site1 (.bind 1 1))]
#guard keeps stP (.bind 1 1) (.bind 1 2)
end PP

/-! ## The reference -/

/-- The reference state related to the checker's at `KP`'s read (identity renaming): the same
frames and positions, `r` holding `0`, `0` lent at `x`'s field `1`. -/
def sRefK : SState :=
  { env := [{}, { binds := List.replicate 5 { ty := .plain .err, val := fun _ => .err } }],
    shape := fun p => if p = .bind 1 4 then some 0 else none,
    nextLoan := 1,
    lent := fun l => if l = 0 then [site1 (.bind 1 3)] else [] }

-- the reference state's holders are the checker's
#guard (allPos stK.env).all fun p => Env.shape stK.env p == if p == .bind 1 4 then some 0 else none

/-- **The reference's read of `x.0` keeps `r`'s borrow** (`readPlace`'s access, `dataHit [.proj 0]`,
at `x`): `0` is still live, held by `r`, with its one site, as in the checker. -/
theorem ref_read_keeps : (sRefK.access (.bind 1 3) (dataHit [.proj 0])).liveLabels = [0] ∧
    (sRefK.access (.bind 1 3) (dataHit [.proj 0])).shape (.bind 1 4) = some 0 ∧
    ((sRefK.access (.bind 1 3) (dataHit [.proj 0])).lent 0).map siteForm = [siteForm (site1 (.bind 1 3))] := by
  decide +kernel

/-- What the checker did before D93 at a non-tail projection, the entry's access of `x` whole,
ends the borrow (the reference never did this, and now need not). -/
theorem ref_whole_ends : (sRefK.access (.bind 1 3) (dataHit [])).liveLabels = [] := by
  decide +kernel

end Ochr.Meaning.Regress.OneCtorEntry
