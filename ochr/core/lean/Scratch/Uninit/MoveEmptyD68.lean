import Ochr.Examples.«00Std»
open Ochr Ochr.Test
/-! docs/10 Q1 experiment (branch uninit-bot-d68 = erased-moves + the uninit-bot checker): the
/-! Not checked on this branch (ochr-core base): it runs on a worktree of `origin/erased-moves`
(D68: statements run with the runtime rules, reads move, no ghosts) with this branch's checker
and fuzzer changes applied (local branch `uninit-bot-d68`, worktree `ochre-uninit-d68`; the
only conflicts were the three `setPlace p .bot` move sites, which become `moveOut p v`, and
`prePassAssert`). Results there (2026-10-01):
* with `moveEmptyByRef` (default): every declaration below as expected. `MTRunEmpty` holds
  (a statement runs the move too), `MTClaim` and `Claim` are refused, `BlockMove` is precise
  at both instances, and the empty value's equations compute (`EmptyEq`, `MovedEq`).
* with `moveEmptyByRef` off: `BlockMoveIn` and `BlockMoveInBoom : False` are accepted. The
  stuck block moves the cell in, which empties it on the generic path although the arm that
  runs at `n = 1` keeps it full (the over-approximation erased-moves met as `Eq ⊥ ⊥`, here a
  wrong value), and `BlockMoveInSplit` is refused.
* fuzzer, `--uninit 100`, seed 1, 2·10⁴ cases, 6 workers: `--switch uninit --switch lentProofs
  --switch moveEmpty` 0 findings (19,857 checked, 143 rejected); the same with
  `moveEmptyByRef` off: 830 `nat`, 226 `false`, 40 `truth`, 188 vacuous; without `moveEmpty`:
  0 findings. On ochr-core (this branch) `moveEmpty` gives 2,674 `exec` findings instead
  (statements copy), and 0 without it. -/
merge's rule 4 where statements move as runtime code does (D68). -/
set_option ochr.uninitTypes true in
set_option ochr.moveEmpty true in
ochr MoveEmptyD68 uses Std {
  untagged inductive Uninit (E : Type) := Empty | Full(x : E)
  def Init (E : Type) (u : Uninit(E)) : Prop := (
    match u {
      Empty => False,
      Full(x) => ⊤,
    }
  )
  -- a move leaves the place empty, and runtime code may read it
  def MoveThenRead (u : Uninit(Nat)) : Uninit(Nat) := (
    let y = u;
    u
  )
  -- the statement runs the move too
  def MTRunEmpty : Id(Uninit(Nat), MoveThenRead(Full(0)), Empty[Nat]) := refl
  reject def MTClaim : Id(Uninit(Nat), MoveThenRead(Full(0)), Full(0)) := refl
  def MT (n : Nat) (u : Uninit(Nat)) : Uninit(Nat) := (
    match n {
      Z => (
        let y = u;
        u
      ),
      S m => u,
    }
  )
  reject def Claim (n : Nat) (u : Uninit(Nat)) : Eq(Uninit(Nat), MT(n, u), u) := (
    match n {
      Z => refl,
      S m => refl,
    }
  )
  -- Q1: a stuck block whose one arm moves the cell out
  def BlockMove (n : Nat) (u : Uninit(Nat)) : Uninit(Nat) := (
    match n {
      Z => (
        let y = u;
        ()
      ),
      S m => (),
    };
    u
  )
  def BlockMoveRun0 : Id(Uninit(Nat), BlockMove(0, Full(1)), Empty[Nat]) := refl
  def BlockMoveRun1 : Id(Uninit(Nat), BlockMove(1, Full(1)), Full(1)) := refl
  reject def BlockMoveLie (n : Nat) : Eq(Uninit(Nat), BlockMove(n, Full(1)), Empty[Nat]) := refl
  reject def BlockMoveLie2 (n : Nat) : Eq(Uninit(Nat), BlockMove(n, Full(1)), Full(1)) := refl
  def BMSpec (n : Nat) : Uninit(Nat) := (
    match n {
      Z => Empty[Nat],
      S m => Full(1),
    }
  )
  def BlockMoveSplit (n : Nat) : Eq(Uninit(Nat), BlockMove(n, Full(1)), BMSpec(n)) := (
    match n {
      Z => refl,
      S m => refl,
    }
  )
  -- the over-approximation, observed: a statement reads the cell right after a stuck block one
  -- of whose arms moves it out. Moved into the block, the cell is empty on this path even where
  -- the arm that runs keeps it full; taken by `&` (moveEmptyByRef), its fill says which
  reject def BlockMoveIn (n : Nat) (u : Uninit(Nat)) :
      Eq(Uninit(Nat), (match n { Z => (let y = u; ()), S m => () }; u), Empty[Nat]) := refl
  reject def BlockMoveInBoom : False := BlockMoveIn(1, Full(1))
  def BlockMoveInSplit (n : Nat) (u : Uninit(Nat)) :
      Eq(Uninit(Nat), (match n { Z => (let y = u; ()), S m => () }; u), (match n { Z => Empty[Nat], S m => u })) := (
    match n {
      Z => refl,
      S m => refl,
    }
  )
  -- the empty value is a value: no stuck equation (D68 makes equations over ⊥ stuck)
  def EmptyEq : Eq(Uninit(Nat), Empty[Nat], Empty[Nat]) := refl
  def MovedEq (u : Uninit(Nat)) : Eq(Uninit(Nat), MoveThenRead(u), Empty[Nat]) := refl
}
def showRows (b : Ochr.Surface.Block) (cfg : Ochr.Config) : List (String × Bool × String) :=
  (run "B" b cfg).rows.map fun r => (r.name, r.expectAccept == r.verdict.ok, match r.verdict with | .accepted => "accepted" | .rejected m _ => m)
#eval showRows MoveEmptyD68 { uninitTypes := true, moveEmpty := true }
#eval showRows MoveEmptyD68 { uninitTypes := true, moveEmpty := true, moveEmptyByRef := false }
