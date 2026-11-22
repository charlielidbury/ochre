import Ochr.Meaning.Steps.Statements
import Ochr.Examples.Nat

/-!
# The access of a place, attacked at the checker's own states (lead26, 2026-11-22; docs/31 D181)

`place`, `borrow` and `assign` share one fact (`Master.AccessG`, `Steps/MasterPlace.lean`): the checker's
[Access] of a place (`accessPath`, then `accessInside`) is the reference's (`SState.access pos (dataHit steps)`).
The reference's access reads only the sites (`lent`) and the holders (the shape): it ends, in rounds and in label
order, every live label with a site on the path, at the place or inside its content, and ending a label re-roots
the sites at its holder (`relend`). So its effect on sites and holders is computable: `SiteSt.access` below is
`SState.access` read on those two fields (`endLabel` forgets the holder and re-roots by `relend`, as `StaticLend`
checked; the meanings it also changes are not computable). Started from the checker's sites (`Env.sitesOf`) and
holders (`findBorrow`), which the relation makes the reference's (`Rel.sites`, `Rel.sim`'s holders), it is
compared with the checker's own access at states the checker holds at a hole in a real program, on the cases the
fragment and the columns did not cover:

1. a field path (a pair with one field lent: the other field's access ends nothing, the field's and the
   whole's end the borrow);
2. a place under a borrow (`*r` with a reborrow `s = &*r`: ends `s`, keeps `r`);
3. a place lent twice: both fields lent (one round ends both) and a chain `x ← r ← s` (two rounds: `r`'s end
   passes its site to `s`);
4. a proof place (a field of a lent record holding a proof: the path ends the record's borrow);
5. a place whose content holds an unknown (a parameter's pair, refined in place to unknowns);
6. a partly moved place (a pair whose first field was moved out, the second lent).

Every case agrees: the same labels end, and every label left live has the same sites and holder. The guard
`agrees` fails where it should: on the reference's access taken at the wrong field (case 1), and on a reference
whose ends do not re-root sites (case 2, `agreesNoRelend`).
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr AccessAt uses Nats {
  inductive Box := MkBox(n : Nat)
  inductive R := MkR(n : Nat, h : Eq(Nat, Z, Z))
  def FieldAt (a : Nat) (b : Nat) : Unit := (let x = (a, b); let r = &x.1; ?)
  def UnderAt (a : Nat) : Unit := (let x = S(a); let r = &x; let s = &*r; ?)
  def TwiceAt (a : Nat) (b : Nat) : Unit := (let x = (a, b); let r0 = &x.0; let r1 = &x.1; ?)
  def ProofAt (a : Nat) : Unit := (let q = MkR(a, refl); let r = &q; ?)
  def UnknownAt (x : Nat × Nat) : Unit := (let r = &x.1; ?)
  def MovedAt (a : Nat) (b : Nat) : Unit := (let x = (MkBox(a), b); let r = &x.1; let y = x.0; ?)
}

namespace Ochr.Meaning.Steps.AccessAttack
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- The checker's whole state at the hole of `name`. -/
def stAt (name : String) : MState :=
  let r := Ochr.Test.runWith (some Prelude) "AccessAt" AccessAt { recordStates := true } (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .state _ false _ st => some st | _ => none).getLast?.getD default
  | none => default

/-- The reference state's sites and holders: the live labels in label order, each one's holder and sites. -/
structure SiteSt where
  live : List Nat
  holder : Nat → Option Pos
  lent : Nat → List Site

/-- `SState.reached` on sites. -/
def SiteSt.reached (S : SiteSt) (p : Pos) (hit : List Step → Bool) (l : Nat) : Bool :=
  (S.lent l).any fun x => decide (x.pos = p) && hit x.path

/-- `SState.endLabel` on sites and holders: the holder forgotten, the sites at it re-rooted (`SState.relend`). -/
def SiteSt.endL (S : SiteSt) (l : Nat) : SiteSt :=
  match S.holder l with
  | some r =>
    let ref : SState := { env := [], shape := fun _ => none, nextLoan := 0, lent := S.lent }
    { live := S.live.erase l, holder := fun m => if m = l then none else S.holder m, lent := ref.relend l r }
  | none => S

/-- `SState.access` on sites and holders. -/
def SiteSt.access (S : SiteSt) (p : Pos) (hit : List Step → Bool) : SiteSt :=
  let step (S : SiteSt) : SiteSt := (S.live.filter (S.reached p hit)).foldl SiteSt.endL S
  (List.range S.live.length).foldl (fun S _ => step S) S

/-- The checker's sites and holders, which the relation makes the reference's (the renaming the identity). -/
def SiteSt.ofEnv (st : MState) : SiteSt :=
  { live := (List.range st.nextLoan).filter (liveLoan st.env), holder := findBorrow st.env, lent := Env.sitesOf st.env }

/-- Two lists of sites hold the same sites, compared by position, the checker's key of the path and kind. -/
def sameSites (xs ys : List Site) : Bool :=
  let eq (x y : Site) : Bool := x.pos == y.pos && walkKey x.path == walkKey y.path && x.fill == y.fill
  xs.all (fun x => ys.any (eq x)) && ys.all (fun y => xs.any (eq y))

/-- The state after a checker step, if it succeeds. -/
def after (x : M Unit) (st : MState) (fuel : Nat) : Option MState :=
  match (runMachine x st fuel).1 with
  | .ok () st' => some st'
  | _ => none

/-- The checker's [Access] of a place, as `readPlace` and `borrowPlace` perform it. -/
def access (p : Place) : M Unit := do accessPath 1000 p; accessInside 1000 p

/-- The labels live after the checker's access of `p`. -/
def liveAfter (st : MState) (p : Place) : Option (List Nat) :=
  (after (access p) st 100000).map fun st' => (List.range st.nextLoan).filter (liveLoan st'.env)

/-- **The checker's access of `p` agrees with the reference's on sites and holders**, the reference's access
taken at the steps `ss` (the place's own, `p.steps.2`, in every guard but the control). -/
def agreesAt (st : MState) (p : Place) (ss : List Step) : Bool :=
  match ckVarPos st.env p.steps.1, after (access p) st 100000 with
  | some pos, some st' =>
    let S' := (SiteSt.ofEnv st).access pos (dataHit ss)
    let live' := (List.range st.nextLoan).filter (liveLoan st'.env)
    live' == S'.live && live'.all fun m => sameSites (Env.sitesOf st'.env m) (S'.lent m) && findBorrow st'.env m == S'.holder m
  | _, _ => false

def agrees (st : MState) (p : Place) : Bool := agreesAt st p p.steps.2

/-- A control: `SiteSt.access` with the ends NOT re-rooting the sites (`relend` dropped). -/
def SiteSt.accessNoRelend (S : SiteSt) (p : Pos) (hit : List Step → Bool) : SiteSt :=
  let endL (S : SiteSt) (l : Nat) : SiteSt :=
    { S with live := S.live.erase l, holder := fun m => if m = l then none else S.holder m, lent := fun m => if m = l then [] else S.lent m }
  let step (S : SiteSt) : SiteSt := (S.live.filter (S.reached p hit)).foldl endL S
  (List.range S.live.length).foldl (fun S _ => step S) S

def agreesNoRelend (st : MState) (p : Place) : Bool :=
  match ckVarPos st.env p.steps.1, after (access p) st 100000 with
  | some pos, some st' =>
    let S' := (SiteSt.ofEnv st).accessNoRelend pos (dataHit p.steps.2)
    let live' := (List.range st.nextLoan).filter (liveLoan st'.env)
    live' == S'.live && live'.all fun m => sameSites (Env.sitesOf st'.env m) (S'.lent m) && findBorrow st'.env m == S'.holder m
  | _, _ => false

/-- A field place of the pair type. -/
def pf (i : Nat) (q : Place) : Place := .field ⟨"Pair", 0, i, ""⟩ q

/-! ### 1. A field path: `x ↦ (σa, loan_0)`, `r ↦ borrow_0 σb` -/
section Field
def st1 : MState := stAt "FieldAt"
#guard (SiteSt.ofEnv st1).live == [0]
-- `x` is variable 1: its field 0 ends nothing, its field 1 and `x` whole end `0`
#guard liveAfter st1 (pf 0 (.var 1)) == some [0]
#guard liveAfter st1 (pf 1 (.var 1)) == some []
#guard liveAfter st1 (.var 1) == some []
#guard agrees st1 (pf 0 (.var 1))
#guard agrees st1 (pf 1 (.var 1))
#guard agrees st1 (.var 1)
-- control: the reference's access at the wrong field disagrees
#guard !agreesAt st1 (pf 1 (.var 1)) [.field ⟨"Pair", 0, 0, ""⟩]
end Field

/-! ### 2. Under a borrow: `x ↦ loan_0`, `r ↦ borrow_0 loan_1`, `s ↦ borrow_1 S(σa)` -/
section Under
def st2 : MState := stAt "UnderAt"
#guard (SiteSt.ofEnv st2).live == [0, 1]
-- `*r` (r is variable 1) ends the reborrow `1` and keeps `0`
#guard liveAfter st2 (.deref (.var 1)) == some [0]
#guard agrees st2 (.deref (.var 1))
-- `*s` ends nothing; `x` ends both, in two rounds (`0`'s end passes its site to `1`)
#guard liveAfter st2 (.deref (.var 0)) == some [0, 1]
#guard agrees st2 (.deref (.var 0))
#guard liveAfter st2 (.var 2) == some []
#guard agrees st2 (.var 2)
-- control: without the re-rooting the reference would end only `0`, and the comparison sees it
#guard !agreesNoRelend st2 (.var 2)
end Under

/-! ### 3. Lent twice: `x ↦ (loan_0, loan_1)`, both fields lent -/
section Twice
def st3 : MState := stAt "TwiceAt"
#guard (SiteSt.ofEnv st3).live == [0, 1]
#guard liveAfter st3 (.var 2) == some []
#guard agrees st3 (.var 2)
#guard liveAfter st3 (pf 0 (.var 2)) == some [1]
#guard agrees st3 (pf 0 (.var 2))
#guard agrees st3 (pf 1 (.var 2))
end Twice

/-! ### 4. A proof place: `q ↦ loan_0` holding `MkR(σa, ⋆)` at `r`'s borrow -/
section Proof
def st4 : MState := stAt "ProofAt"
#guard (SiteSt.ofEnv st4).live == [0]
#guard liveAfter st4 (.field ⟨"R", 0, 1, "h"⟩ (.var 1)) == some []
#guard agrees st4 (.field ⟨"R", 0, 1, "h"⟩ (.var 1))
#guard agrees st4 (.deref (.var 0))
end Proof

/-! ### 5. Content with unknowns: a parameter pair refined in place, `x ↦ (σ, loan_0)` -/
section Unknown
def st5 : MState := stAt "UnknownAt"
#guard (SiteSt.ofEnv st5).live == [0]
#guard liveAfter st5 (pf 0 (.var 1)) == some [0]
#guard agrees st5 (pf 0 (.var 1))
#guard agrees st5 (.var 1)
end Unknown

/-! ### 6. Partly moved: `x ↦ (⊥, loan_0)` -/
section Moved
def st6 : MState := stAt "MovedAt"
#guard (SiteSt.ofEnv st6).live == [0]
#guard liveAfter st6 (.var 2) == some []
#guard agrees st6 (.var 2)
#guard agrees st6 (pf 0 (.var 2))
end Moved

end Ochr.Meaning.Steps.AccessAttack
