import Ochr.Runtime
import Ochr.Test
open Ochr Ochr.Test Ochr.Surface

/-!
# Probe (Target B, type safety): an accepted data function whose closed run errs

Found with the runtime's entry point (`Ochr/Runtime.lean`, `runCall`, D85) on main 7ae8cf00
(re-checked on f4254ad8). `JoinMv` is accepted, yet its closed run at `n = 1`, on closed `Nat`
arguments, with no proofs and no function arguments, errs:
"[Join] p is moved by another arm of the match, so it is dropped at the end of this one, while
the arm's result borrows it". The checker's own untyped run errs the same way (`closedCall … false`),
so this is not [J-run]'s doing.

Mechanism (from `cfg.derivation`'s trace of `JoinMv`):
- At the generic call `n` is unknown, so the match, which is not in tail position, is closed off as
  the stuck block `fix _ (n : Nat) (p : Nat) (q : &Nat) : &Nat := match n { Z => let z = p; &*q,
  S _ => &p }`. The block takes `p` BY MOVE, because arm `Z` moves it, and `q` by `&`.
- Arm `S` returns `&p`, a borrow of the block's own by-value parameter. `closeBlock`'s [Return]
  accepts it ("a stuck match's arm returns it: borrow_1 σ1 : &Nat"): the block's return does not
  apply the in-flight check that a function's does (D65: "[Drop] p dies while a value in flight
  borrows it"), nor D84's [Join]. The block's result then ties only `q`'s lender; `p`'s borrow is
  gone from the derivation.
- At the closed call the match is on a known constructor, and D84's [Join] drops `p` at the end of
  arm `S`, which the arm's result borrows: the run errs.
- The two paths disagree inside the checker too: the generic `JoinMv` (and `Caller`, at an unknown
  `n`) is accepted, while the instance `AtS : Nat := JoinMv(1, 0, 0)` is rejected with that same
  message.
So docs/29's lemma that the derivation is at least as strict as the run fails here, and not at a
one-element type: these are `Nat` places. **Fixed by D87.** `closeBlock` now rejects an arm whose result borrows a place the block takes by
move, with the direct path's [Join] message, so `JoinMv` is rejected where its block forms and
both paths agree. The twin `JoinLent`, where no arm moves `p` (so the block takes it by `&`),
is accepted, and its closed runs return at both `n`.

Run: `lake env lean ../probes/runtime/JoinHitRepro.lean` from `ochr/core/lean`, after
`lake build Ochr`. Expected output: none (silent). The `ochr` block asserts the verdicts and the
`#guard`s assert the rejection's message and the runtime's results; any output means the
behaviour changed.
-/

ochr JoinHit {
  reject def JoinMv (n : Nat) (p : Nat) (q : Nat) : Nat := (let r = match n { Z => (let z = p; &q), S _ => &p }; *r := 1; q)
  def JoinLent (n : Nat) (p : Nat) (q : Nat) : Nat := (let r = match n { Z => (let z = clone(p); &q), S _ => &p }; *r := 1; q)
  def Caller (n : Nat) : Nat := JoinLent(n, 0, 0)
  def AtS : Nat := JoinLent(1, 0, 0)
}

-- JoinMv is rejected where its block forms, with the direct path's [Join] message (D87)
#guard (run "JoinHit" JoinHit).rejectedWith [
  ("JoinMv", "[Join] p is moved by another arm of the match, so it is dropped at the end of this one, while the arm's result borrows it")]

def sig : List GDef × List IndDecl :=
  let p := libOf {} 2000000 JoinHit ++ JoinHit.decls
  globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)

def returns (k : Nat) : Outcome Value → Bool
  | .ok v _ => v == (List.range k).foldl (fun v _ => .succ v) .zero
  | _ => false

-- the twin's closed runs return: at n = 1 arm S writes 1 into p and returns q = 0, at n = 0 it
-- writes 1 into q
#guard returns 0 (runCall sig.1 sig.2 "JoinLent" [.succ .zero, .zero, .zero])
#guard returns 1 (runCall sig.1 sig.2 "JoinLent" [.zero, .zero, .zero])
#guard returns 0 (runCall sig.1 sig.2 "Caller" [.succ .zero])
#guard returns 0 (closedCall sig.1 sig.2 "JoinLent" [.succ .zero, .zero, .zero] false)
