import Ochr.Meaning.DataModel.Exists.Defs
import Ochr.Meaning.DataModel.Canonical.Knot

/-!
# Membership is monotone in weaker proposition leaves (exists6)

`General.mono_prop` (piece 5's single step), proved: a declaration whose record at `ps'` has, at every
key, the shape it has at `ps` or a proposition leaf implied by the one at `ps`, has a member at `ps'`
when it has one at `ps`. The member is the same constructor with the same fields: a proof field fits any
proposition leaf it is a proof of (`encLeaf` of a proposition code is `⋆`).

The statement's content is in its hypothesis `hcanon` (`ShapeLe` at every key): the induction over
declarations must establish it for the construction's records. It can hold only where every shape a
nestable `Prop` parameter reaches is a proposition leaf or a `Prop`-sorted sub-record, which rule (A*) (a nested occurrence passes only through declarations of
its own sort; `CrossSortCE.lean`) guarantees and the checker does not yet enforce: for `E2 (P : Prop) :
Prop := MkE2(w : Wrap(P))` the shape at `w` is a data sub-record that depends on `P`. The parameter
lists' relation `hle` is not needed by the step.
-/

namespace Ochr.Meaning.DataModel.Exists

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical

/-- Parameter lists that differ only at nestable `Prop` parameters, each weakened. -/
def PropLe (d : IndDecl) (ps ps' : List Sem) : Prop :=
  ps'.length = ps.length ∧ ∀ j v v', ps[j]? = some v → ps'[j]? = some v' →
    v' = v ∨ (d.nestable.getD j false = true ∧
      ∃ P P' : Prop, v = .ty (TyM.prop P) ∧ v' = .ty (TyM.prop P') ∧ (P → P'))

/-- A shape weaker than another for fitting: the same, a proposition leaf implied by the other, or a
`Prop`-sorted sub-record inhabited when the other is (a `prf` field asks only that its declaration be
inhabited). -/
def ShapeLe (sh sh' : Shape) : Prop :=
  sh' = sh ∨ (∃ P P' : Prop, (P → P') ∧ sh = .leaf (PLift P) (.prop P) ∧ sh' = .leaf (PLift P') (.prop P')) ∨
    ∃ (M : IndDecl) (q q' : Rec), ((∃ v, DataLib.Mem uSig M q v) → ∃ v, DataLib.Mem uSig M q' v) ∧
      sh = .prf M q ∧ sh' = .prf M q'

/-- Fitting carries over to a record whose shapes are weaker (`ShapeLe`). -/
theorem fitsM_mono {d : IndDecl} {r r' : Rec} {c : Nat}
    (h : ∀ i es, ShapeLe (uShape d r c i es) (uShape d r' c i es)) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), FitsM uSig d r c i n e fs → FitsM uSig d r' c i n e fs
  | 0, _, _, _, hf => hf
  | n + 1, i, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fitsM_mono h n (i + 1) _ fs' h2⟩
    show FitsOneM uSig (uShape d r' c i e) f
    change FitsOneM uSig (uShape d r c i e) f at h1
    rcases h i e with he | ⟨P, P', hPP, hs, hs'⟩ | ⟨M, q, q', hq, hs, hs'⟩
    · rw [he]; exact h1
    · rw [hs] at h1
      rw [hs']
      obtain ⟨b, hb⟩ := h1
      exact ⟨⟨hPP b.down⟩, hb⟩
    · rw [hs] at h1
      rw [hs']
      exact ⟨h1.1, hq h1.2⟩

/-- `fitsM_mono` with the shapes compared at the genuine keys only (the earlier readings as many as the
field's index), which are all fitting reads (exists7). -/
theorem fitsM_mono' {d : IndDecl} {r r' : Rec} {c : Nat}
    (h : ∀ i es, es.length = i → ShapeLe (uShape d r c i es) (uShape d r' c i es)) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), e.length = i → FitsM uSig d r c i n e fs → FitsM uSig d r' c i n e fs
  | 0, _, _, _, _, hf => hf
  | n + 1, i, e, fs, he, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fitsM_mono' h n (i + 1) _ fs' (by simp [he]) h2⟩
    show FitsOneM uSig (uShape d r' c i e) f
    change FitsOneM uSig (uShape d r c i e) f at h1
    rcases h i e he with he' | ⟨P, P', hPP, hs, hs'⟩ | ⟨M, q, q', hq, hs, hs'⟩
    · rw [he']; exact h1
    · rw [hs] at h1
      rw [hs']
      obtain ⟨b, hb⟩ := h1
      exact ⟨⟨hPP b.down⟩, hb⟩
    · rw [hs] at h1
      rw [hs']
      exact ⟨h1.1, hq h1.2⟩

/-- **Membership is monotone in weaker shapes** (`General.mono_prop`, proved and generalized by exists6
from proposition leaves to `ShapeLe`, which also admits `Prop`-sorted sub-records: a `Prop`-sorted
declaration nested in another keeps it as a `prf` shape; the parameter relation `hle` is not used). -/
theorem mono_prop (dm : DataModel) (d : IndDecl) (ps ps' : List Sem)
    (hcanon : ∀ c i es, ShapeLe (uShape d (dm.recOf d ps) c i es) (uShape d (dm.recOf d ps') c i es))
    (_hle : PropLe d ps ps') :
    (∃ v, dm.Mem d (dm.recOf d ps) v) → ∃ v, dm.Mem d (dm.recOf d ps') v := by
  rintro ⟨v, hv⟩
  obtain ⟨c, fs, rfl, hf⟩ := (DataLib.mem_iff uSig d _ v).1 hv
  exact ⟨_, (DataLib.mem_iff uSig d _ _).2 ⟨c, fs, rfl, fitsM_mono (hcanon c) _ 0 [] fs hf⟩⟩

end Ochr.Meaning.DataModel.Exists
