import Ochr.Meaning.SState
import Ochr.Examples.Nat
import Ochr.Examples.Fixtures

/-!
# Static lending, on the checker's own states (built)

docs/31 D29 (fifth lead, 2026-11-19). The reference lends statically, as main's D90 checker does:
each borrow has its sites (`SState.lent`), [Access] ends the borrows with a site at the place it
reads, [End] passes the ended borrow's sites to the borrows of its final content (`relend`), and a
borrow-returning call lends its result every place its borrow arguments lend, each a fill
(`callOfL`). The relation asks the reference's sites to be the checker's (`Env.sitesOf`). Two
attacks on that design, run on the states the checker itself reaches:

* **A reborrow that outlives its borrow (D90's G8).** `r = Pick(n, &a, &b)` at an unknown `n`,
  then `s = &*r`. When `r` ends, `s` must keep both `a` and `b` lent, so that `clone(a)` ends `s`
  and the write `*s := 4` after it is an error (`G8`, rejected), while the write before the read
  is fine (`G8Ok`). At a known `n` (`G8K`, `G8KOk`) the same.
* **A borrow-returning call at a known argument (Pick at Z).** `r = Pick(Z, &a, &b)` points into
  `a`, but `b` must stay lent to `r`, so that `clone(b)` ends `r` (`PZ`, rejected; `PZOk`).

The checker's states are the ones it holds at a hole `?` placed at the point (the editor's Ω, read
back from the real run of the real program, `atHole`). On each the checks are:

1. after the call, the result's sites in the checker are the reference's (`lentK`: the arguments'
   sites, each a fill);
2. after [End] of `r`'s borrow, the checker's `endBorrow` and the reference's `relend` and
   `semEnd` leave every label at the same sites and the same holders (the relation's `sites`
   clause and the holders part of its `sim` clause; the meanings part is not computable);
3. reading the lender ends the reborrow: the reference reaches it there (`reached`), and the
   checker's access of the place ends it.

All hold. The instance states (`G8K`, `PZ`) hold no sealed program, and the kernel checks them
(`decide +kernel`): the sites, the holders, the checker's own `endBorrow` run on the state (without
the library's globals: nothing in it calls one) against the reference's `relend`, and the
reference's `reached`. The checker's reads are evaluated (`#guard`): its [Access]
(`firstLiveLoanOnPath`) is well-founded recursion, which the kernel does not unfold. The generic
`G8`'s fills are sealed programs whose re-normalisation calls `Pick`, so all of it is evaluated,
with the library's globals. A `#guard` ties each hand-written state to the run's.
-/

open Ochr.Test

ochr StaticLend uses Nats, Fixtures {
  reject def G8 (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b); let s = &*r; let z = clone(a); *s := 4; ())
  def G8Ok (n : Nat) (a : Nat) (b : Nat) : Unit := (
    let r = Pick(n, &a, &b); let s = &*r; *s := 4; let z = clone(a); ())
  reject def G8K (a : Nat) (b : Nat) : Unit := (
    let r = Pick(S(Z), &a, &b); let s = &*r; let z = clone(a); *s := 4; ())
  def G8KOk (a : Nat) (b : Nat) : Unit := (
    let r = Pick(S(Z), &a, &b); let s = &*r; *s := 4; let z = clone(a); ())
  reject def PZ (a : Nat) (b : Nat) : Unit := (
    let r = Pick(Z, &a, &b); let z = clone(b); *r := 1; ())
  def PZOk (a : Nat) (b : Nat) : Unit := (
    let r = Pick(Z, &a, &b); *r := 1; let z = clone(b); ())
}

-- the points the checks look at, as holes (accepted: a hole is an axiom)
#guard_msgs (drop warning) in
ochr StaticLendAt uses Nats, Fixtures {
  def G8At (n : Nat) (a : Nat) (b : Nat) : Unit := (let r = Pick(n, &a, &b); let s = &*r; ?)
  def G8KAt (a : Nat) (b : Nat) : Unit := (let r = Pick(S(Z), &a, &b); let s = &*r; ?)
  def PZAt (a : Nat) (b : Nat) : Unit := (let r = Pick(Z, &a, &b); ?)
}

namespace Ochr.Meaning.Regress.StaticLend
open Ochr Ochr.Meaning

/-- The values of the bindings the checker holds at the hole of `name` (the editor's Ω, from the
real run of `StaticLendAt`; the function's own binding is left out). -/
def atHole (name : String) : List Value :=
  let r := Ochr.Test.runWith (some Prelude) "StaticLendAt" StaticLendAt (located := true)
  match r.rows.find? (·.name == name) with
  | some row => (row.trace.toList.filterMap fun
      | .note _ _ (.hole _ Ω) => some (Ω.map (·.2.2)) | _ => none).headD []
  | none => []

/-- The library's globals and inductive types (`Pick`, `Nat`). -/
def libGlobals : List GDef × List IndDecl :=
  let p := libOf {} 2000000 StaticLendAt
  globalsAfter {} (p.filterMap fun d => match (Ochr.Surface.runResolve p d 2000000 false).1 with
    | .ok (.ok df) => some df | _ => none)

/-- The checker's state at a hole: frame 0 holds no cell (no borrow parameter); frame 1 the
function's own binding, then the bindings at the hole; `k` labels and `σ₀ … σ_{a-1} : Nat` issued. -/
def stateAt (self : String) (vs : List Value) (k a : Nat) (gl : Bool := false) : MState :=
  { env := #[{}, { binds := #[({ hint := ⟨self⟩, ty := none, val := .gfn self } : Binding)] ++
      (vs.map fun v => ({ hint := ⟨"x"⟩, ty := some .tNat, val := v } : Binding)).toArray }],
    -- main's D96: each unknown's reading frozen when it was made (`Nat`'s is `.other`)
    nextLoan := k, absTy := Array.replicate a .tNat, absDecl := Array.replicate a .other, nextAbs := a,
    globals := if gl then libGlobals.1 else [], inds := if gl then libGlobals.2 else [] }

/-- Two lists of sites hold the same sites (as sets: the relation's `sites` clause). -/
def sameSites (xs ys : List Site) : Bool :=
  let eq (x y : Site) : Bool := x.pos == y.pos && x.path == y.path && x.fill == y.fill
  xs.all (fun x => ys.any (eq x)) && ys.all (fun y => xs.any (eq y))

/-- The reference's lending where the relation holds with the renaming the identity: the
checker's sites (only `lent` is read below). -/
def refOf (env : Env) (lent : Nat → List Site := Env.sitesOf env) : SState :=
  { env := [], shape := fun _ => none, nextLoan := 0, lent }

/-- The state after a checker step from `st`, if it succeeds. -/
def after (x : M Unit) (st : MState) (fuel : Nat) : Option MState :=
  match (runMachine x st fuel).1 with
  | .ok () st' => some st'
  | _ => none

/-- (2) [End l] at the holder `r`: after the checker's `endBorrow`, every label below the counter
is lent at the sites the reference's `relend` gives it, and the holders are the reference's
(`semEnd` forgets `r`, and nothing else). -/
def endAgrees (st : MState) (l : Nat) (r : Pos) (fuel : Nat) : Bool :=
  match after (endBorrow fuel l) st (fuel * 10) with
  | some st' =>
    (List.range st.nextLoan).all (fun m => sameSites (Env.sitesOf st'.env m) ((refOf st.env).relend l r m)) &&
    (allPos st.env).all (fun p => Env.shape st'.env p == if p == r then none else Env.shape st.env p)
  | none => false

/-- The checker's read of the variable `x` (de Bruijn): its access, `accessPath` then
`accessInside`, as `clone(x)` performs it. -/
def read (fuel x : Nat) : M Unit := do accessPath fuel (.var x); accessInside fuel (.var x)

/-- The labels the checker has live after the step `x`. -/
def liveAfter (x : M Unit) (st : MState) (fuel : Nat) : Option (List Nat) :=
  (after x st fuel).map fun st' => (List.range st.nextLoan).filter (liveLoan st'.env)

/-- The sites `&p` gives a place `p` held at `q` (`borrowPlace`: one plain site), made fills by a
borrow-returning call (`callOfL`'s `lentK`). -/
def lentK (qs : List Pos) : List Site := qs.map fun q => ⟨q, [], true⟩

/-! ## The reborrow that outlives its borrow, at an unknown `n` (D90's G8)

At the hole: `n ↦ ⊥` (moved into the call), `a ↦ ⌈…; *r := loan_3; c1⌉`, `b ↦ ⌈…; c2⌉` (the
closed-off call's fills over `3`), `r ↦ borrow_3 loan_4`, `s ↦ borrow_4 ⌈…; *r⌉`. -/

section G8
def st8 : MState := stateAt "G8At" (atHole "G8At") 5 3 (gl := true)
def a8 : Pos := .bind 1 2
def b8 : Pos := .bind 1 3
def r8 : Pos := .bind 1 4

-- the run reached the hole with five bindings, `r` holding `3` and `s` holding `4`
#guard (atHole "G8At").length == 5
#guard Env.shape st8.env r8 == some 3 && Env.shape st8.env (.bind 1 5) == some 4
-- (1) the call lent its result `a` and `b`, as fills, as the reference's call does
#guard sameSites (Env.sitesOf st8.env 3) (lentK [a8, b8])
-- (2) [End 3]: the reborrow `4`, lent at `*r` before, is lent at `a` and `b` after, on both sides
#guard sameSites (Env.sitesOf st8.env 4) [⟨r8, [.deref], false⟩]
#guard endAgrees st8 3 r8 100000
-- (3) after [End 3], reading `a` ends `4`: the reference reaches it at `a`, the checker ends it
#guard (refOf st8.env ((refOf st8.env).relend 3 r8)).reached a8 (dataHit []) 4
#guard liveAfter (do endBorrow 100000 3; read 100000 3) st8 2000000 == some []
-- the program's order (`G8`): `clone(a)` while `r` is live ends `3` (reached at `a`), whose sites
-- pass to `4`, which the next round ends; the checker's read ends both
#guard (refOf st8.env).reached a8 (dataHit []) 3 && !(refOf st8.env).reached a8 (dataHit []) 4
#guard liveAfter (read 100000 3) st8 2000000 == some []
end G8

/-! ## The same at a known `n` (`G8K`), kernel-checked

At the hole: `a ↦ lent_1 σ0` (a known fill over `1`: `a`'s value, which `r` does not point into),
`b ↦ lent_1 loan_1` (the identity: `r` points into `b`), `r ↦ borrow_1 loan_3`, `s ↦ borrow_3 σ1`. -/

section G8K
def vK : List Value := [.gloan 1 (.abs 0), .gloan 1 (.loan 1), .borrow 1 (.loan 3), .borrow 3 (.abs 1)]
#guard atHole "G8KAt" == vK
def stK : MState := stateAt "G8KAt" vK 4 2
def aK : Pos := .bind 1 1
def bK : Pos := .bind 1 2
def rK : Pos := .bind 1 3

-- the library's globals change nothing here
#guard endAgrees (stateAt "G8KAt" vK 4 2 (gl := true)) 1 rK 100000

theorem g8k_holders : Env.shape stK.env rK = some 1 ∧ Env.shape stK.env (.bind 1 4) = some 3 := by
  decide +kernel
/-- (1) the call lent its result `a` and `b`, as fills, as the reference's call does. -/
theorem g8k_call : sameSites (Env.sitesOf stK.env 1) (lentK [aK, bK]) = true := by decide +kernel
/-- (2) [End 1]: the reborrow `3`, lent at `*r` before, is lent at `a` and `b` after, on both sides,
and the holders agree. -/
theorem g8k_end : sameSites (Env.sitesOf stK.env 3) [⟨rK, [.deref], false⟩] = true ∧
    endAgrees stK 1 rK 50 = true := by decide +kernel
/-- (3) after [End 1], reading `a` ends `3`: the reference reaches it at `a`; the checker's read
ends it (`#guard` below). -/
theorem g8k_read_after_end : (refOf stK.env ((refOf stK.env).relend 1 rK)).reached aK (dataHit []) 3 = true := by
  decide +kernel
/-- The program's order (`G8K`): reading `a` while `r` is live ends `1` (reached at `a`), whose sites
pass to `3`, which the next round ends; the checker's read ends both (`#guard` below). -/
theorem g8k_read : (refOf stK.env).reached aK (dataHit []) 1 = true ∧
    (refOf stK.env).reached aK (dataHit []) 3 = false := by decide +kernel
-- the checker's reads: its [Access] (`firstLiveLoanOnPath`) is well-founded recursion, which the
-- kernel does not unfold, so they are evaluated
#guard liveAfter (do endBorrow 50 1; read 50 3) stK 1000 == some []
#guard liveAfter (read 50 3) stK 1000 == some []
end G8K

/-! ## A borrow-returning call at a known argument (Pick at `Z`), kernel-checked

At the hole: `a ↦ lent_0 loan_0` (the identity: `r` points into `a`), `b ↦ lent_0 σ1` (a known
fill over `0`: `b`'s value), `r ↦ borrow_0 σ0`. The place the result does not point into, `b`, is
a site of `r`'s borrow, and reading it ends that borrow. -/

section PZ
def vZ : List Value := [.gloan 0 (.loan 0), .gloan 0 (.abs 1), .borrow 0 (.abs 0)]
#guard atHole "PZAt" == vZ
def stZ : MState := stateAt "PZAt" vZ 2 2
def aZ : Pos := .bind 1 1
def bZ : Pos := .bind 1 2

#guard liveAfter (read 100000 1) (stateAt "PZAt" vZ 2 2 (gl := true)) 2000000 == some []

/-- (1) the call lent its result `a` and `b`, as fills, as the reference's call does: `b` is a site
though the result does not point into it. -/
theorem pz_call : Env.shape stZ.env (.bind 1 3) = some 0 ∧
    sameSites (Env.sitesOf stZ.env 0) (lentK [aZ, bZ]) = true := by decide +kernel
/-- (3) reading `b` ends the result's borrow: the reference reaches it at `b`; the checker's read
ends it (`#guard` below, as for `G8K`). -/
theorem pz_read : (refOf stZ.env).reached bZ (dataHit []) 0 = true := by decide +kernel
#guard liveAfter (read 50 1) stZ 1000 == some []
end PZ

end Ochr.Meaning.Regress.StaticLend
