import Ochr.Meaning.Steps.Machine.ReadInv
import Ochr.Meaning.Steps.ColumnJ

/-!
# The decisions `I`'s type reads, at every fuel (machine8; leaves of `CallJInv`, `FixRunI`, `ConstRunJ`)

`Π(n : Nat). Nat` (`ColumnI.piNat`) as the checker reads it at every fuel where the reading succeeds:
`Nat`'s declared sort is `Type₀` (`declOf`: `.sort 1`), so its reading as a type is data (`typeDecl`:
`.other`), the function's class is data (`fnClass`: `0`), it is no proposition (`isPropV`), its kind
is data (`declKind`), and its one parameter reads `.other`, no proof (`paramDecls`, `paramFlags`).
Each reads the state and writes nothing (`decideKeep`).
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem runs_declOf_nat {k : Nat} {chk : Bool} {sc : List DeclInfo} {ns : List String} {st st' : MState} {b : Nat}
    {d : DeclInfo} (h : Runs (Ochr.declOf k chk sc ns .nat) st b d st') : d = .sort 1 ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.declOf at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.declOf at h; exact runs_pure_inv h

theorem runs_typeDecl_nat {k : Nat} {chk : Bool} {sc : List DeclInfo} {ns : List String} {vis : List String}
    {tsc : List (Option DeclInfo)} {st st' : MState} {b : Nat} {d : DeclInfo}
    (h : Runs (Ochr.typeDecl k chk sc ns .nat vis tsc) st b d st') : d = .other ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.typeDecl at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.typeDecl at h
    obtain ⟨d', s₁, b₁, hd, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_declOf_nat hd
    exact runs_pure_inv h₁


theorem runs_typePos_keep {k : Nat} {chk : Bool} {sc : List DeclInfo} {ns : List String} {T : Term} {st st' : MState}
    {b l : Nat} (h : Runs (Ochr.typePos k chk sc ns T) st b l st') : st' = st :=
  runs_keep ((decideKeep k).2.2.2.2.2.2.2.2.2.2.2.1 _ _ _ _) h

theorem runs_telescope_nat {k : Nat} {chk : Bool} {sc : List DeclInfo} {ns : List String} {h : Hint} {st st' : MState}
    {b : Nat} {r : List DeclInfo × List String × Nat} (hr : Runs (Ochr.telescope k chk sc ns [h] [.nat]) st b r st') :
    r.1 = .other :: sc ∧ r.2.1 = h.name :: ns ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.telescope at hr; simp only [runs_exhausted_iff] at hr
  | succ k =>
    unfold Ochr.telescope at hr
    simp only [List.zip, List.zipWith, List.forIn_cons, List.forIn_nil, bind_assoc] at hr
    obtain ⟨l, s₁, b₁, hp, h₁⟩ := Runs.bind_inv hr
    have := runs_typePos_keep hp; subst this
    obtain ⟨d, s₂, b₂, hd, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨rfl, rfl⟩ := runs_typeDecl_nat hd
    simp only [pure_bind] at h₂
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₂
    exact ⟨rfl, rfl, rfl⟩

/-- `Π(n : Nat). Nat` is a function type whose calls return data (class `0`). -/
theorem runs_fnClass_piNat {k : Nat} {st st' : MState} {b c : Nat} (h : Runs (Ochr.fnClass k ColumnI.piNat) st b c st') :
    c = 0 ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.fnClass at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.fnClass ColumnI.piNat at h
    simp only at h
    obtain ⟨cs, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    have := runs_keep (keep_capReadings _ _) hc; subst this
    obtain ⟨r, s₂, b₂, ht, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨-, -, rfl⟩ := runs_telescope_nat ht
    obtain ⟨d, s₃, b₃, hd, h₃⟩ := Runs.bind_inv h₂
    obtain ⟨rfl, rfl⟩ := runs_typeDecl_nat hd
    exact runs_pure_inv h₃

theorem runs_isPropV_piNat {k : Nat} {st st' : MState} {b : Nat} {p : Bool}
    (h : Runs (Ochr.isPropV k ColumnI.piNat) st b p st') : p = false ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.isPropV at h; simp only [runs_exhausted_iff] at h
  | succ k =>
    unfold Ochr.isPropV ColumnI.piNat at h
    obtain ⟨c, s₁, b₁, hc, h₁⟩ := Runs.bind_inv h
    obtain ⟨rfl, rfl⟩ := runs_fnClass_piNat hc
    exact runs_pure_inv h₁

theorem runs_isPropV_nat {k : Nat} {st st' : MState} {b : Nat} {p : Bool}
    (h : Runs (Ochr.isPropV k .tNat) st b p st') : p = false ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.isPropV at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.isPropV at h; exact runs_pure_inv h

theorem runs_declKind_piNat {k : Nat} {st st' : MState} {b : Nat} {r : Kind}
    (h : Runs (Ochr.declKind k ColumnI.piNat) st b r st') : r = .data ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.declKind at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.declKind ColumnI.piNat at h; exact runs_pure_inv h

theorem runs_paramFlags_nat {k : Nat} {st st' : MState} {b : Nat} {r : List Bool}
    (h : Runs (Ochr.paramFlags k [] [] [.nat]) st b r st') : r = [false] ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.paramFlags at h; simp only [runs_exhausted_iff] at h
  | succ k => unfold Ochr.paramFlags at h; simp only [List.all_cons, List.all_nil] at h; exact runs_pure_inv h

theorem runs_paramDecls_nat {k : Nat} {h : Hint} {st st' : MState} {b : Nat} {r : List DeclInfo × DeclInfo}
    (hr : Runs (Ochr.paramDecls k [] [] [h] [.nat] .nat) st b r st') : r = ([.other], .other) ∧ st' = st := by
  cases k with
  | zero => unfold Ochr.paramDecls at hr; simp only [runs_exhausted_iff] at hr
  | succ k =>
    unfold Ochr.paramDecls at hr
    obtain ⟨cs, s₁, b₁, hc, h₁⟩ := Runs.bind_inv hr
    have := runs_keep (keep_capReadings _ _) hc; subst this
    have hcs : cs = [] := by
      unfold capReadings at hc; simp only [List.length_nil, Nat.lt_irrefl, if_false] at hc
      exact (runs_pure_inv (by simpa using hc)).1
    subst hcs
    obtain ⟨r', s₂, b₂, ht, h₂⟩ := Runs.bind_inv h₁
    obtain ⟨e1, -, rfl⟩ := runs_telescope_nat ht
    obtain ⟨d, s₃, b₃, hd, h₃⟩ := Runs.bind_inv h₂
    obtain ⟨rfl, rfl⟩ := runs_typeDecl_nat hd
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₃
    simp [e1]

end Ochr.Meaning.Steps.Machine
