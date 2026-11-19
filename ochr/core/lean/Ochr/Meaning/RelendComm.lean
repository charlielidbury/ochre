import Ochr.Meaning.SState

/-!
# Ends commute on sites (docs/31 D29 point 3; `dropOne_step`'s obligation 3)

[End ℓ] at the holder `r` passes the sites under `r`'s content to `ℓ`'s sites (`SState.relend`).
The reference ends the borrows an access reaches in label order, the checker in its own; the sites
come out the same in either order when neither borrow is lent at the other's holder (the
acyclicity of (WF3), on sites), and every site at a holder lies inside its content (a holder holds
a borrow, `&&T` is outside the core). `endLabel_comm` is the meanings' half.
-/

namespace Ochr.Meaning

/-- What [End] at `(l, r)` does to one site `x` of another borrow. -/
def relendOne (L : Nat → List Site) (l : Nat) (r : Pos) (x : Site) : List Site :=
  match x.path with
  | .deref :: π =>
    if x.pos = r then (L l).map fun y => if y.fill then y else { y with path := y.path ++ π, fill := x.fill }
    else [x]
  | _ => [x]

theorem relend_eq (s : SState) (l : Nat) (r : Pos) (m : Nat) :
    s.relend l r m = if m = l then [] else (s.lent m).flatMap (relendOne s.lent l r) := by
  unfold SState.relend relendOne; rfl

/-- The lent function after [End] at `(l, r)`. -/
def relendL (L : Nat → List Site) (l : Nat) (r : Pos) : Nat → List Site := fun m =>
  if m = l then [] else (L m).flatMap (relendOne L l r)

theorem relendOne_off {L : Nat → List Site} {l : Nat} {r : Pos} {x : Site} (h : x.pos ≠ r) :
    relendOne L l r x = [x] := by
  unfold relendOne; split <;> simp [h]

/-- How [End] adjusts one of the ended borrow's sites `y` for a site `x` with path `* :: π`. -/
def adjust (x : Site) (π : List Step) (y : Site) : Site :=
  if y.fill then y else { y with path := y.path ++ π, fill := x.fill }

theorem adjust_pos (x : Site) (π : List Step) (y : Site) : (adjust x π y).pos = y.pos := by
  unfold adjust; split <;> rfl

theorem relendOne_at {L : Nat → List Site} {l : Nat} {r : Pos} {x : Site} {π : List Step}
    (hp : x.path = .deref :: π) (hx : x.pos = r) : relendOne L l r x = (L l).map (adjust x π) := by
  unfold relendOne adjust; simp [hp, hx]

theorem flatMap_congr' {α β : Type _} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), flatMap_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem flatMap_off {L : Nat → List Site} {l : Nat} {r : Pos} {xs : List Site} (h : ∀ y ∈ xs, y.pos ≠ r) :
    xs.flatMap (relendOne L l r) = xs := by
  rw [flatMap_congr' (g := fun y => [y]) fun y hy => relendOne_off (h y hy)]
  simp

/-- One site at `k`'s holder, ended in either order. -/
theorem relendOne_comm_at (L : Nat → List Site) (k l : Nat) (rk rl : Pos) (hkl : k ≠ l) (hr : rk ≠ rl)
    (hin_k : ∀ y ∈ L k, y.pos = rl → ∃ π, y.path = .deref :: π)
    (hacyc : (∀ y ∈ L l, y.pos ≠ rk) ∨ (∀ y ∈ L k, y.pos ≠ rl)) (x : Site) (hx : x.pos = rk) :
    (relendOne L k rk x).flatMap (relendOne (relendL L k rk) l rl) =
      (relendOne L l rl x).flatMap (relendOne (relendL L l rl) k rk) := by
  have hxl : x.pos ≠ rl := hx ▸ hr
  rw [relendOne_off (L := L) (l := l) hxl, List.flatMap_singleton]
  rcases hp : x.path with _ | ⟨st, π⟩
  · unfold relendOne; simp [hp]
  · cases st with
    | proj _ | field _ => unfold relendOne; simp [hp]
    | deref =>
      rw [relendOne_at hp hx, relendOne_at hp hx, List.flatMap_map]
      simp only [relendL, if_neg hkl, List.map_flatMap]
      refine flatMap_congr' fun y0 hy0 => ?_
      by_cases hy0r : y0.pos = rl
      · have h1 : ∀ y ∈ L l, y.pos ≠ rk := by
          rcases hacyc with h1 | h2
          · exact h1
          · exact absurd hy0r (h2 y0 hy0)
        obtain ⟨π0, hπ0⟩ := hin_k y0 hy0 hy0r
        rw [relendOne_at hπ0 hy0r, List.map_map]
        have hRk : relendL L k rk l = L l := by simp only [relendL, if_neg hkl.symm]; exact flatMap_off h1
        by_cases hf : y0.fill
        · have e : adjust x π y0 = y0 := by simp [adjust, hf]
          rw [e, relendOne_at hπ0 hy0r, hRk]
          refine List.map_congr_left fun z _ => ?_
          by_cases hz : z.fill <;> simp [adjust, hz, hf]
        · have hp' : (adjust x π y0).path = .deref :: (π0 ++ π) := by simp [adjust, hf, hπ0]
          rw [relendOne_at hp' (by rw [adjust_pos]; exact hy0r), hRk]
          refine List.map_congr_left fun z _ => ?_
          by_cases hz : z.fill <;> simp [adjust, hz, hf, List.append_assoc]
      · rw [relendOne_off hy0r, relendOne_off (by rw [adjust_pos]; exact hy0r)]
        rfl

/-- **Ends commute on sites**: ending `k` at its holder `rk` and `l` at `rl` in either order leaves
every borrow lent at the same sites (as lists), when every site at either holder lies inside its
content and one of the two is not lent at the other's holder (acyclicity). -/
theorem relendL_comm (L : Nat → List Site) (k l : Nat) (rk rl : Pos) (hkl : k ≠ l) (hr : rk ≠ rl)
    (hin_k : ∀ y ∈ L k, y.pos = rl → ∃ π, y.path = .deref :: π)
    (hin_l : ∀ y ∈ L l, y.pos = rk → ∃ π, y.path = .deref :: π)
    (hacyc : (∀ y ∈ L l, y.pos ≠ rk) ∨ (∀ y ∈ L k, y.pos ≠ rl)) :
    relendL (relendL L k rk) l rl = relendL (relendL L l rl) k rk := by
  funext m
  by_cases hml : m = l
  · subst hml; simp [relendL, hkl.symm]
  by_cases hmk : m = k
  · subst hmk; simp [relendL, hkl]
  simp only [relendL, if_neg hml, if_neg hmk, List.flatMap_assoc]
  refine flatMap_congr' fun x _ => ?_
  by_cases hxk : x.pos = rk
  · exact relendOne_comm_at L k l rk rl hkl hr hin_k hacyc x hxk
  by_cases hxl : x.pos = rl
  · exact (relendOne_comm_at L l k rl rk (Ne.symm hkl) (Ne.symm hr) hin_l hacyc.symm x hxl).symm
  rw [relendOne_off hxk, relendOne_off hxl, List.flatMap_singleton, List.flatMap_singleton,
    relendOne_off hxl, relendOne_off hxk]

/-- The same, on reference states: `relend` after `relend`. -/
theorem relend_comm (s : SState) (k l : Nat) (rk rl : Pos) (hkl : k ≠ l) (hr : rk ≠ rl)
    (hin_k : ∀ y ∈ s.lent k, y.pos = rl → ∃ π, y.path = .deref :: π)
    (hin_l : ∀ y ∈ s.lent l, y.pos = rk → ∃ π, y.path = .deref :: π)
    (hacyc : (∀ y ∈ s.lent l, y.pos ≠ rk) ∨ (∀ y ∈ s.lent k, y.pos ≠ rl)) :
    ({ s with lent := s.relend k rk } : SState).relend l rl =
      ({ s with lent := s.relend l rl } : SState).relend k rk := by
  have e : ∀ (t : SState) (a : Nat) (r : Pos), t.relend a r = relendL t.lent a r := fun t a r => by
    funext m; rw [relend_eq]; rfl
  rw [e, e]
  show relendL (s.relend k rk) l rl = relendL (s.relend l rl) k rk
  rw [e, e]
  exact relendL_comm s.lent k l rk rl hkl hr hin_k hin_l hacyc

end Ochr.Meaning
