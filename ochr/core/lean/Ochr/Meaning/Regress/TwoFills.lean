import Ochr.Meaning.WF
import Ochr.Meaning.SState
import Ochr.Examples.Nat

/-!
# Two live fills at one place (built; (WF12) as restated in D33 is false since D93)

docs/31 D39 (fifth lead, 2026-11-21). (WF12) was restated after the first sweep (D33) to what that
sweep measured: at a position holding a live fill, no other live borrow has a site at the fill's
path or below it. Main's D93 made `SweepProbes.LentUnder.TwoParts` accepted:

```
let c = (1, 2); let e = (0, 0); let r = Whole(&c);
let a = IdN(&(*r).0); let b = &(*r).1; *a := 3; *b := 4; r := &e; let d = c; d
```

Two disjoint parts of the returned borrow `r`'s place are lent onward, to `a` and `b`. When `r` is
re-pointed its borrow ends, and its mark at `c` passes to every live borrow its content was lent
onward to (D90's [End]), so both are filled at `c` whole: `c = lent_2 (lent_4 (lent_2 loan_2,
loan_4))`, `a = borrow_2 3`, `b = borrow_4 4`. Each is a live fill with the other's site at the same
path. The sweep's mirror of D33's form reports it (3 probe states); the state below is the shape of
the recorded one (the sites and labels; the probe's own state is compared with `#guard`).

The form (WF12) now has (`WF.lean`): every live borrow with a site at or below a live fill's path
has a fill at that path. Both borrows here do. It is what the absorption of the lent prefix needs
(`AccessAbsorb.AbsorbInv`, `DropOne.lentPrefix_fill`), and the proof of `lentPrefix_fill` is
shorter with it.
-/

open Ochr.Test

-- the probe, as in `SweepProbes.lean`'s `LentUnder` (accepted since D93)
ochr TwoFillsProbe uses Nats {
  def Whole (x : &(Nat × Nat)) : &(Nat × Nat) := x
  def IdN (x : &Nat) : &Nat := x
  def TwoParts : Nat × Nat := (
    let c = (1, 2);
    let e = (0, 0);
    let r = Whole(&c);
    let a = IdN(&(*r).0);
    let b = &(*r).1;
    *a := 3;
    *b := 4;
    r := &e;
    let d = c; d)
}

namespace Ochr.Meaning.Regress.TwoFills
open Ochr Ochr.Meaning

/-- (WF12) as restated in D33 (spine 81cf4a9e – 6eb1dab4). -/
def WF12D33 (env : Env) : Prop :=
  ∀ k l, liveLoan env k = true → liveLoan env l = true → k ≠ l →
    ∀ x ∈ Env.sitesOf env k, x.fill = true → ∀ y ∈ Env.sitesOf env l, y.pos = x.pos →
      (pathKey x.path).isPrefixOf (pathKey y.path) = false

def pair (a b : Value) : Value := .ind "Pair" 0 ⟨"MkPair"⟩ [.tNat, .tNat] [a, b]

/-- `c = lent_2 (lent_4 (lent_2 loan_2, loan_4))`, `a = borrow_2 3`, `b = borrow_4 4` (frame 0). -/
def envTP : Env :=
  #[{ binds := #[
      { hint := ⟨"c"⟩, ty := none, val := .gloan 2 (.gloan 4 (pair (.gloan 2 (.loan 2)) (.loan 4))) },
      { hint := ⟨"a"⟩, ty := none, val := .borrow 2 (.succ (.succ (.succ .zero))) },
      { hint := ⟨"b"⟩, ty := none, val := .borrow 4 (.succ (.succ (.succ (.succ .zero)))) }] }]

theorem live : liveLoan envTP 2 = true ∧ liveLoan envTP 4 = true := by decide +kernel

/-- A fill at `c` whole. -/
def atC : Pos → Bool
  | .bind 0 0 => true
  | _ => false

theorem atC_eq {p : Pos} (h : atC p = true) : p = .bind 0 0 := by
  unfold atC at h; split at h <;> first | rfl | cases h

def fillAtC (x : Site) : Bool := atC x.pos && x.path.isEmpty && x.fill

theorem fills_b : (Env.sitesOf envTP 2).any fillAtC = true ∧ (Env.sitesOf envTP 4).any fillAtC = true := by
  constructor <;> decide +kernel

theorem fill_of {l : Nat} (h : (Env.sitesOf envTP l).any fillAtC = true) :
    ∃ x ∈ Env.sitesOf envTP l, x.pos = .bind 0 0 ∧ x.path = [] ∧ x.fill = true := by
  obtain ⟨x, hx, hf⟩ := List.any_eq_true.mp h
  simp only [fillAtC, Bool.and_eq_true, List.isEmpty_iff] at hf
  exact ⟨x, hx, atC_eq hf.1.1, hf.1.2, hf.2⟩

theorem not_wf12D33 : ¬ WF12D33 envTP := by
  intro h
  obtain ⟨x, hx, hxp, hxs, hxf⟩ := fill_of fills_b.1
  obtain ⟨y, hy, hyp, hys, -⟩ := fill_of fills_b.2
  have := h 2 4 live.1 live.2 (by decide) x hx hxf y hy (hyp.trans hxp.symm)
  simp [pathKey, hxs, hys] at this

/-- **(WF12) as it now stands holds of the two fills**: each borrow with a site at or below the
other's fill is filled at that path (here, at `c` whole, both ways). -/
theorem wf12_here : (∃ x ∈ Env.sitesOf envTP 2, x.pos = .bind 0 0 ∧ x.path = [] ∧ x.fill = true) ∧
    (∃ x ∈ Env.sitesOf envTP 4, x.pos = .bind 0 0 ∧ x.path = [] ∧ x.fill = true) :=
  ⟨fill_of fills_b.1, fill_of fills_b.2⟩

/-! ## The probe's own state -/

/-- The checker's states while running `TwoParts` (recorded). -/
def tpStates : List MState :=
  let r := Ochr.Test.runWith (some Prelude) "TwoFillsProbe" TwoFillsProbe { recordStates := true } (located := true)
  match r.rows.find? (·.name == "TwoParts") with
  | some row => row.trace.toList.filterMap fun | .state _ _ _ st => some st | _ => none
  | none => []

/-- Some recorded state has two live borrows, each with a fill at the same position and path. -/
def twoFillsAt (st : MState) : Bool :=
  let live := (List.range st.nextLoan).filter (liveLoan st.env)
  live.any fun k => live.any fun l => k != l &&
    (Env.sitesOf st.env k).any fun x => x.fill && (Env.sitesOf st.env l).any fun y =>
      y.fill && y.pos == x.pos && pathKey y.path == pathKey x.path

#guard tpStates.any twoFillsAt

end Ochr.Meaning.Regress.TwoFills
