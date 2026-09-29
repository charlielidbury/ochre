import Ochr.Examples.«00Std»

/-! # Unit tests of individual rules, run directly on the machine functions

Not part of the tour: these call the checker's functions on hand-built values, for
[Seal] (a sealed program re-runs when a refinement is substituted) and for the owners and
footprint of RULES §4. The programs they need (`AddM`, `TailM`) come from
`Std`. -/

open Ochr Ochr.Test Ochr.Surface

namespace Ochr.Units

/-- The globals after checking a block (its library first). -/
def globalsOf (b : Block) : List GDef :=
  let p := Ochr.Test.libOf {} 2000000 b ++ b.decls
  (globalsAfter {} (p.filterMap fun d => (resolveProgram p d).toOption)).1

def st (b : Block) (nAbs : Nat) : MState :=
  { globals := globalsOf b, nextAbs := nAbs, absTy := (List.replicate nAbs Value.tNat).toArray }

def ok? {α : Type} : Except String α → Option α
  | .ok a => some a
  | .error _ => none

/-- `N(v, w) := ⌈let c1 = v; AddM(&c1, w); c1⌉`, what [Close] leaves in `AddM`'s borrowed place
(with D53 on, the final read of `c1` is an observation, `peek`, which copies; these run with
the default rules, where D53 is off). -/
def N (v w : Value) : Value :=
  .sealed (.letIn ⟨"c1"⟩ (.val v) (.seq (.call (.val (.gfn "AddM")) [.borrow (.var 0), .val w] true) (.place (.var 0))))

/-- `B(v)[h] := ⌈let c1 = v; let r = TailM(&c1); *r := h; c1⌉`, `TailM`'s effect with its hole. -/
def B (v h : Value) : Value :=
  .sealed (.letIn ⟨"c1"⟩ (.val v) (.letIn ⟨"r"⟩ (.call (.val (.gfn "TailM")) [.borrow (.var 0)] true)
    (.seq (.assign (.deref (.var 0)) (.val h)) (.place (.var 1)))))

-- [Seal] (D9): refining σ0 := S σ1 re-runs N(σ0, 0); the inner call closes off, the
-- head call does not, so the S surfaces (deriver-e1 lemma S2)
#guard ok? (runM (substV (.abs 0) (.succ (.abs 1)) (N (.abs 0) .zero)) (st Std 2)) == some (.succ (N (.abs 1) .zero))
-- deriver-e1 S1: N(0, 0) ≡ 0
#guard ok? (runM (substV (.abs 0) .zero (N (.abs 0) .zero)) (st Std 1)) == some .zero
-- deriver-e1 S0: N(σ, 0) is normal (its own head call is not closed off again: no loop)
#guard ok? (runM (substV (.abs 5) .zero (N (.abs 0) .zero)) (st Std 6)) == some (N (.abs 0) .zero)
-- deriver-e2 §3.4: B(S σ1)[τ] ≡ S B(σ1)[τ]
#guard ok? (runM (substV (.abs 0) (.succ (.abs 1)) (B (.abs 0) (.abs 2))) (st Std 3)) == some (.succ (B (.abs 1) (.abs 2)))
-- deriver-e2 F3 / D11: a loan whose borrow is outside the [Seal] run is inert: B(0)[loan_9] ≡ loan_9
#guard ok? (runM (substV (.abs 0) .zero (B (.abs 0) (.loan 9))) (st Std 1)) == some (.loan 9)
-- ending the borrow fills the hole by substitution and re-normalises (D11)
#guard ok? (runM (substV (.loan 9) (.abs 2) (B .zero (.loan 9))) (st Std 3)) == some (.abs 2)

-- D18: owners(ℓ) is a set. Ω = [a ↦ S loan_5, b ↦ ⌈… loan_5 …⌉, r ↦ borrow_5 0]
def envD18 : Env := #[{ binds := #[{ hint := ⟨"a"⟩, ty := some .tNat, val := .succ (.loan 5) },
                                  { hint := ⟨"b"⟩, ty := some .tNat, val := .sealed (.val (.loan 5)) },
                                  { hint := ⟨"r"⟩, ty := some (.tRef .tNat), val := .borrow 5 .zero }] }]
#guard owners envD18 5 == [.bind 0 0, .bind 0 1]
-- W(*r := 0, *r := 1) observes both owners; the single-owner reading keeps one
#guard footprint envD18 [.assign (.deref (.var 0)) .zero, .assign (.deref (.var 0)) (.succ .zero)] == [.bind 0 0, .bind 0 1]
#guard footprint envD18 [.assign (.deref (.var 0)) .zero] false == [.bind 0 0]
-- an occurrence inside another borrow's content contributes that borrow's owners
def envChain : Env := #[{ binds := #[{ hint := ⟨"c"⟩, ty := some .tNat, val := .loan 0 }] },
                        { binds := #[{ hint := ⟨"x"⟩, ty := some (.tRef .tNat), val := .borrow 0 (.succ (.loan 1)) },
                                     { hint := ⟨"x'"⟩, ty := some (.tRef .tNat), val := .borrow 1 (.abs 0) }] }]
#guard owners envChain 1 == [.bind 0 0]

end Ochr.Units

/-! ## Blocks that use other blocks

`AttrUser` uses `AttrLib`. Only `AttrLib`'s accepted, non-`reject` declarations are visible
to it; they are checked again in `AttrUser` under the same configuration. When a rule is
switched off (here D45's matching by type) and `Swap` flips, the flip is attributed to its
home block, and `UseSwap`, which fails only because `Swap` is gone, is reported as blocked. -/

ochr AttrLib {
  def Swap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := match h { Intro(a, b) => ⟨b, a⟩ }
  reject def Hidden : Nat := ()
}

ochr AttrUser uses AttrLib {
  def UseSwap (P : Prop) (Q : Prop) (h : P ∧ Q) : Q ∧ P := Swap(P, Q, h)
  def Alone : Nat := 0
  -- a `reject` declaration of a used block is not visible
  reject def SeesHidden : Nat := Hidden
}

open Ochr.Test in
#guard (run "AttrLib" AttrLib).allAsExpected && (run "AttrLib" AttrLib).count == 2
-- a block's report has rows for its own declarations only
open Ochr.Test in
#guard (run "AttrUser" AttrUser).allAsExpected && (run "AttrUser" AttrUser).count == 3
open Ochr.Test in
#guard blockFlips "AttrLib" AttrLib { byType := false } == (["AttrLib.Swap:rejected"], [])
open Ochr.Test in
#guard blockFlips "AttrUser" AttrUser { byType := false } == ([], ["AttrUser.UseSwap blocked by AttrLib.Swap"])

-- one flat namespace: redeclaring a name a used block declares is a clash (the `ochr` command
-- reports it when the block is elaborated), but a `reject` declaration of the used block is
-- not in the namespace
open Ochr.Surface in
#guard (Block.mk "Clashy" [AttrLib] [{ name := "Swap", expectAccept := true }]).clashes ==
  ["Clashy declares Swap, which AttrLib (used by Clashy) already declares; the declarations of a block and the blocks it uses share one namespace"]
open Ochr.Surface in
#guard (Block.mk "NoClash" [AttrLib] [{ name := "Hidden", expectAccept := true }]).clashes == []
open Ochr.Surface in
#guard (Block.mk "Twice" [AttrLib, AttrUser] []).closure.map (·.name) == ["AttrLib", "AttrUser"]
