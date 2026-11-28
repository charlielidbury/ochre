import Ochr.Meaning.Run
import Ochr.Test
import Ochr.Meaning.Regress.GenNeutralContent

/-!
# The general match step, attacked on the real checker (lead41, 2026-11-28; docs/31 D248)

Programs chosen to break the statements of `Steps/MasterMatch.lean` (the match on a known constructor, the split
on an unknown at the end of a body, `split f in u`, the match on a proof), each run through the real checker.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr MatchAtk {
  inductive Bool := false | true
  inductive Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))
  def Payload (b : Bool) : Type := match b { false => Nat, true => Unit, }
  inductive DP := MkDP(b : Bool, x : Payload(b))
  def IsZ (n : Nat) : Bool := match n { Z => true, S(m) => false, }
  -- 1. arms that move different places (a tail split; each world's join drops both)
  def A1 (x : Nat) (y : Nat) (n : Nat) : Nat := match n { Z => x, S(m) => y, }
  -- 2. an arm that ends a borrow the other keeps
  def A2 (n : Nat) (a : Nat) : Nat := (let r = &a; match n { Z => (let z = clone(a); z), S(m) => (*r := 1; 0), })
  -- 3. a field of a dependent pair: the inner split refines the type of the other field
  def A3 (d : DP) : Nat := match d { MkDP(b, x) => match b { false => clone(x), true => 0, }, }
  -- 4. a scrutinee under a borrow, an arm writing through the pattern variable
  def A4 (x : &Nat) : Nat := match *x { Z => 0, S(p) => (p := Z; 1), }
  -- 5. nested splits, the inner on the outer's field
  def A5 (n : Nat) : Nat := match n { Z => 0, S(m) => match m { Z => 1, S(k) => clone(k), }, }
  -- 6. an arm impossible in its world
  def A6 (n : Nat) (h : Eq(Nat, n, Z)) : Nat := match n { Z => 0, S(m) => match h {}, }
  -- 7. a borrow-typed match on a known constructor (entry, lending), not in tail position
  def A7 (x : &Nat) (y : &Nat) : Unit := (let n = Z; let r : &Nat = match n { Z => x, S(m) => y, }; *r := 5)
  -- 8. the same unknown split twice
  def A8 (n : Nat) : Nat := match n { Z => match n { Z => 0, S(m) => 1, }, S(m) => 2, }
  -- 9. a lemma whose tail-shaped body writes a parameter (the reference erases it whole)
  def L9 (n : Nat) : True := (n := 5; refl)
  -- 10. a match on a proof in tail position whose arm writes a parameter
  def P10 (e : Ex) (n : Nat) : True := match e { Wit(w, h) => (n := 5; refl), }
  -- 11. a known constructor, not in tail position, arms moving different places
  def A11 (x : Nat) (y : Nat) : Nat := (let n = Z; let r = match n { Z => x, S(m) => y, }; r)
  -- 12. a split on a sealed scrutinee (generalised) at the end of a body
  def A12 (n : Nat) : Nat := (let b = IsZ(n); match b { false => 1, true => 2, })
  -- 13. `split f in u`; a hypothesis about the split result refined in each world
  def Pk (n : Nat) : Nat := (let b = IsZ(n); match b { false => 1, true => 2, })
  def A13 (n : Nat) : Eq(Bool, IsZ(Pk(n)), false) := split IsZ in refl
  def A13h (n : Nat) (h : Eq(Bool, IsZ(n), true)) : Eq(Nat, Pk(n), 2) := split IsZ(n) { false => match h {}, true => refl, }
  -- 15. a match the table reads as a proof whose arm moves a parameter inside a proof: its join is empty
  def L11 (n : Nat) (y : Nat) : True := match n { Z => (let k = y; refl), S(m) => refl, }
  -- 14. a split whose arms leave the scrutinee's pattern variable moved and refilled
  def A14 (n : Nat) (y : Nat) : Nat := match n { Z => y, S(m) => (let k = m; m := k; y), }
}

namespace Ochr.Meaning.Steps.MatchAtk

open Ochr Ochr.Meaning
open Ochr.Meaning.Regress.GenNeutralContent (isOk outSt outVal)

-- every verdict as expected: all accepted
#guard ((Ochr.Test.runWith (some Prelude) "MatchAtk" MatchAtk {} (located := false)).allAsExpected)

/-- The resolved body of a definition of the block. -/
def bodyOf (name : String) : Term :=
  match MatchAtk.decls.find? (·.name == name) with
  | some d => match Ochr.Surface.runResolve MatchAtk.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

/-- The checker's recorded state at the entry of a definition's body (its frame: the function's binding of itself,
then `np` parameters). -/
def entryOf (nm : String) (np : Nat) : Option MState :=
  let r := Ochr.Test.runWith (some Prelude) "MatchAtk" MatchAtk { recordStates := true } (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => (row.trace.toList.filterMap fun e => match e with
      | .state _ _ _ st => if st.env.size == 2 && st.env[1]!.binds.size == np + 1 then some st else none
      | _ => none).head?
  | none => none

/-! ## Finding 1: the end-of-body check of a lemma keeps the effects of its tail-shaped body; the reference erases it

`L9 (n : Nat) : True := (n := 5; refl)` is accepted. Its body is a sequence whose declared type is `True`, a declared
proof: the pre-pass reads it `(true, true)` (`Decide.preFlags`), so the reference, at any table aligned with the
checker's, runs it under `SM.erasedIf` and RESTORES its state (`runT_tailShaped_erased_state` below). The checker's
`checkFix` checks the body by `checkTail`, which recurses into the sequence by its shape (`checkTailAt`'s `.seq`) and
runs `n := 5` on the real state: the leaf where the [Def] continuation runs holds `n ↦ 5` (guard `L9leaf`). So `TailAt`
(`Steps/Master.lean`) is false there: for the continuation `kHolds5 1` (which succeeds exactly where the top frame's
binding 1 holds `5`), every leaf `TailOutK` may name holds `n ↦ 5`, while the reference's state after is the start's,
where `n` means the assignment's `σ0`; `Rel.sim` compares the two at `n`. A match on a proof in tail position is the same
(`P10`: its arm writes the parameter; the reference does not even run the arm, D229). -/

/-- `5`. -/
def five : Value := .succ (.succ (.succ (.succ (.succ .zero))))

/-- A continuation that succeeds exactly where the top frame's binding `i` holds `5` and the value is `⋆` at `⊤`. -/
def kHolds5 (i : Nat) : Value → Value → M Unit := fun v T => do
  let st ← get
  if st.env[st.env.size - 1]!.binds[i]!.val == five && v == .proof && T == .tInd "True" [] then pure () else err "k"

-- `L9`'s body is the sequence `#0 := 5; refl`, checked from `n ↦ σ0` at the goal `⊤`, one erased depth down
#guard (bodyOf "L9").pp [] == "#0 := 5; refl"
#guard (entryOf "L9" 1).any fun st => st.env[1]!.binds[1]!.val == .abs 0 && st.goal == some (.tInd "True" []) &&
  st.erasedDepth == 1
-- the pre-pass reads the body as a proof: erased, a proof
#guard (entryOf "L9" 1).any fun st =>
  match outVal (do let d ← withLive true (Ochr.declOf 100 false [] [] (bodyOf "L9")); Ochr.preFlags (bodyOf "L9") d)
    st 100000 with
  | some (e, p) => e && p
  | none => false
-- L9leaf: the end-of-body check succeeds with a continuation that needs `n ↦ 5` at the leaf (and fails with one that
-- needs anything else there)
#guard (entryOf "L9" 1).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "L9") (kHolds5 1)) st 100000
#guard (entryOf "L9" 1).any fun st => !isOk (Ochr.checkTail 1000 (bodyOf "L9")
  (fun _ _ => do if (← get).env[1]!.binds[1]!.val == .abs 0 then pure () else err "k")) st 100000
-- P10: a match on a proof (of `Ex`, not a subsingleton) at the end of a lemma; its arm writes `n`: the leaf holds `5`
#guard (bodyOf "P10").pp [] == "match #1 { Wit => #0 := 5; refl }"
#guard (entryOf "P10" 2).any fun st => isOk (Ochr.checkTail 1000 (bodyOf "P10") (kHolds5 2)) st 100000

-- L11: the static join of a match the table reads as a proof is empty (its arms are statements)
#guard (entryOf "L11" 2).any fun st => (outVal (Ochr.staticJoin 100 (bodyOf "L11")) st 100000).1.isEmpty

/-- An erased run (a statement, or a proof) leaves the state it started from. -/
theorem erasedIf_state {fl : Bool × Bool} {x : SM (Sem × TyS)} {s s' : SState} {r : Sem × TyS}
    (hfl : fl.1 = true ∨ fl.2 = true) (h : SM.erasedIf fl x s = some (r, s')) : s' = s := by
  unfold SM.erasedIf at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · cases h
    · cases h
  · rename_i h2
    have h1 : fl.1 = true := by rcases hfl with h | h; exact h; simp [h] at h2
    rcases SM.stmtIf_some h with ⟨e, -⟩ | ⟨-, e, -⟩
    · rw [h1] at e; cases e
    · exact e

/-- **The reference's run of a tail-shaped term the table erases leaves the state it started from** (`let`, `;`, the
two matches; whatever the tail flag): the half of Finding 1 on the model's side. -/
theorem runT_tailShaped_erased_state (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (t : Term)
    (ht : (∃ x u w, t = .letIn x u w) ∨ (∃ u w, t = .seq u w) ∨ (∃ p z u, t = .matchNat p z u) ∨
      (∃ p n arms, t = .matchInd p n arms))
    (s s' : SState) (r : Res) (hfl : (K.D.flags (scopeOf s) t).1 = true ∨ (K.D.flags (scopeOf s) t).2 = true)
    (h : runT K ρ φ tl hint t s = some (r, s')) : s' = s := by
  rcases ht with ⟨x, u, w, rfl⟩ | ⟨u, w, rfl⟩ | ⟨p, z, u, rfl⟩ | ⟨p, n, arms, rfl⟩ <;>
    (rw [runT] at h; exact erasedIf_state hfl h)

end Ochr.Meaning.Steps.MatchAtk
