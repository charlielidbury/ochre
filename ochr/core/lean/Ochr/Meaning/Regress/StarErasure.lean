import Ochr.Meaning.SitesWrite
import Ochr.Meaning.AccessAbsorb
import Ochr.Examples.Nat

/-!
# Two statements that `*`-erasure made false (docs/31 D67; kernel-checked, kept as records)

The lead's (a): compare paths with `*` erased (`pathKey`). Two proved statements depended on the
positional comparison and were false under erasure, each at a state the checker never reaches.
Both are stated here with the erased key written out (`keyE`), so they hold whatever `pathKey` is.
The lead's resolution: `relend` re-roots every site at the holder (the first holds again,
`absorb_endLabel_now`); the checker's statements about its own values keep the positional key
(`walkKey`), meeting the reference's in the relation (`KeyBridge`). The checker's rejection that
makes both states unreachable is asserted below (`StarErasureProbe`).

* **`AccessAbsorb.AbsorbInv.endLabel`** (the absorption invariant survives an end). When the
  ended borrow's holder `r` is itself lent at a path NOT under its `*` (here at `[]`) as well as at
  `[*]`, the erased keys of the two sites are equal; [End] as first written (`relendOld`) re-roots
  only the site under the `*`, so after it the site at `[]` has no fill at its key
  (`absorb_endLabel_fails`). A site at
  a borrow holder not under its `*` is a borrow of a borrow-typed place, which the checker rejects
  ("a borrow of a borrow-typed place").
* **`SitesWrite.sitesOf_updAt_bot`** (the write of `⊥` removes exactly the sites at or under the
  written path). At a mark directly over a borrow, `gloan 0 (borrow 1 Z)`, the write at `[*]`
  keeps the mark's site at `[]`, whose erased key is the written path's (`updAt_bot_fails`). A mark
  directly over a borrow is a borrow-typed place lent whole, which the checker rejects likewise.
-/

namespace Ochr.Meaning.Regress.StarErasure
open Ochr Ochr.Meaning

/-- A path's field keys with its `*`s erased. -/
def keyE (ψ : List Step) : List (Nat × Nat) := ψ.filterMap Step.key

/-- `AbsorbInv` with the erased key. -/
def AbsorbInvE (s : SState) (pos : Pos) (K : List (Nat × Nat)) : Prop :=
  (∀ m ∈ s.liveLabels, ∀ x ∈ s.lent m, x.pos = pos → keyE x.path <+: K → keyE x.path = K) ∧
  (∀ m ∈ s.liveLabels, ∀ x ∈ s.lent m, x.pos = pos → K <+: keyE x.path →
    ∃ y ∈ s.lent m, y.pos = pos ∧ keyE y.path = K ∧ y.fill = true)

/-- `q` lent to `0` (plain); `r` holds `0` and is lent to `1` at `[]` and, as a fill, at `[*]`;
`h` holds `1`. -/
def SA : SState :=
  { env := [SFrame.mk [{ ty := .plain TyM.nat, val := fun _ => .el0 Nat 0 },
      { ty := ⟨TyM.nat, some 0⟩, val := fun ψ => ψ 1 }, { ty := ⟨TyM.nat, some 1⟩, val := fun _ => .el0 Nat 0 }] []],
    shape := fun p => if p = .bind 0 1 then some 0 else if p = .bind 0 2 then some 1 else none,
    nextLoan := 2,
    lent := fun m => if m = 0 then [⟨.bind 0 0, [], false⟩]
      else if m = 1 then [⟨.bind 0 1, [], false⟩, ⟨.bind 0 1, [.deref], true⟩] else [] }

theorem positions_SA : SA.positions = [.bind 0 0, .bind 0 1, .bind 0 2] := by
  simp [SA, SState.positions, List.range']

theorem find_SA : SA.positions.find? (fun p => decide (SA.shape p = some 0)) = some (.bind 0 1) := by
  rw [positions_SA]; simp [SA]

theorem live_SA {m : Nat} (hm : m ∈ SA.liveLabels) : m = 0 ∨ m = 1 := by
  obtain ⟨p, hp, hs⟩ := (SState.mem_liveLabels SA m).1 hm
  rw [positions_SA] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp [SA] at hs <;> omega

theorem absorb_SA : AbsorbInvE SA (.bind 0 1) [] := by
  refine ⟨fun m _ x _ _ h => List.prefix_nil.mp h, fun m hm x hx hxp _ => ?_⟩
  rcases live_SA hm with rfl | rfl
  · simp [SA] at hx; rw [hx] at hxp; simp at hxp
  · exact ⟨⟨.bind 0 1, [.deref], true⟩, by simp [SA], rfl, rfl, rfl⟩

/-- [End] on sites as first written: only the sites under the holder's `*` re-rooted. -/
def relendOld (s : SState) (l : Nat) (r : Pos) : Nat → List Site := fun m =>
  if m = l then [] else (s.lent m).flatMap fun x =>
    match x.path with
    | .deref :: π =>
      if x.pos = r then (s.lent l).map fun y => if y.fill then y else { y with path := y.path ++ π, fill := x.fill }
      else [x]
    | _ => [x]

theorem live_end_SA : 1 ∈ (SA.endLabel 0).liveLabels := by
  rw [SState.mem_liveLabels, SState.positions_endLabel, SState.endLabel_shape SA 0 _ find_SA, positions_SA]
  exact ⟨.bind 0 2, by simp, by simp [SA]⟩

/-- **The absorption invariant did not survive [End] as first written, under erasure**: after `0`
ends at `r`, `1`'s site `(r, [])` stayed and its fill `(r, [*])` moved to `q`. -/
theorem absorb_endLabel_fails : AbsorbInvE SA (.bind 0 1) [] ∧
    ¬ AbsorbInvE { SA.endLabel 0 with lent := relendOld SA 0 (.bind 0 1) } (.bind 0 1) [] := by
  refine ⟨absorb_SA, fun h => ?_⟩
  have hlent : relendOld SA 0 (.bind 0 1) 1 = [⟨.bind 0 1, [], false⟩, ⟨.bind 0 0, [], true⟩] := by
    simp [relendOld, SA]
  obtain ⟨y, hy, hyp, -, hyf⟩ := h.2 1 live_end_SA ⟨.bind 0 1, [], false⟩
    (by show _ ∈ relendOld SA 0 (.bind 0 1) 1; rw [hlent]; simp) rfl (List.nil_prefix)
  change y ∈ relendOld SA 0 (.bind 0 1) 1 at hy
  rw [hlent] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · cases hyf
  · simp at hyp

/-- **With [End] re-rooting every site at the holder it survives**: both of `1`'s sites at `r` pass
to `q`, and nothing is left at `r`. -/
theorem absorb_endLabel_now : AbsorbInvE (SA.endLabel 0) (.bind 0 1) [] := by
  have hlent : (SA.endLabel 0).lent 1 = [⟨.bind 0 0, [], false⟩, ⟨.bind 0 0, [], true⟩] := by
    rw [SState.lent_endLabel find_SA]
    simp [SState.relend, SA, inContent]
  have hlent0 : (SA.endLabel 0).lent 0 = [] := by
    rw [SState.lent_endLabel find_SA]; simp [SState.relend]
  refine ⟨fun m _ x _ _ h => List.prefix_nil.mp h, fun m hm x hx hxp _ => ?_⟩
  rcases live_SA (SState.mem_liveLabels_of_endLabel hm) with rfl | rfl
  · rw [hlent0] at hx; cases hx
  · rw [hlent] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp at hxp

/-- **The write of `⊥` does not remove exactly the sites under it, under erasure**: at the mark
`gloan 0 (borrow 1 Z)`, the write at `[*]` keeps the mark's site at `[]`, whose erased key is the
written path's. -/
theorem updAt_bot_fails :
    ∃ v', Value.updAt (fun _ => .bot) [.deref] (.gloan 0 (.borrow 1 .zero)) = some v' ∧
      ¬ ∀ x, x ∈ Value.sitesOf 0 (.bind 0 0) [] v' ↔
        (x ∈ Value.sitesOf 0 (.bind 0 0) [] (.gloan 0 (.borrow 1 .zero)) ∧
          ¬ (keyE ([] ++ [.deref])).isPrefixOf (keyE x.path) = true) := by
  refine ⟨.gloan 0 (.borrow 1 .bot), by simp [Value.updAt], fun h => ?_⟩
  have := (h ⟨.bind 0 0, [], true⟩).1 (by simp [Value.sitesOf])
  simp [keyE, Step.key] at this

end Ochr.Meaning.Regress.StarErasure

/-! The checker's rejection that keeps both states out of reach: a borrow-typed place is never
lent whole (a reborrow goes through `*`), beside the accepted reborrow. -/

open Ochr.Test in
ochr StarErasureProbe uses Nats {
  reject def BorrowOfBorrow (a : Nat) : Unit := (let r = &a; let s = &r; ())
  def Reborrow (a : Nat) : Unit := (let r = &a; let s = &*r; ())
}
