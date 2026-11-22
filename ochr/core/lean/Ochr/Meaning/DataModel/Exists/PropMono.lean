import Ochr.Meaning.DataModel.Exists.Defs
import Ochr.Meaning.DataModel.Canonical.Knot

/-!
# Membership is monotone in weaker proposition leaves (exists6)

`General.mono_prop` (piece 5's single step), proved: a declaration whose record at `ps'` has, at every
key, the shape it has at `ps` or a proposition leaf implied by the one at `ps`, has a member at `ps'`
when it has one at `ps`. The member is the same constructor with the same fields: a proof field fits any
proposition leaf it is a proof of (`encLeaf` of a proposition code is `⋆`).

The statement's content is in its hypothesis `hcanon`: the induction over declarations must establish
it for the construction's records. It can hold only where every shape a nestable `Prop` parameter
reaches is a proposition leaf, which rule (A*) (a nested occurrence passes only through declarations of
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

/-- Fitting carries over to a record whose shapes are the same or weaker proposition leaves. -/
theorem fitsM_mono {d : IndDecl} {r r' : Rec} {c : Nat}
    (h : ∀ i es, uShape d r' c i es = uShape d r c i es ∨ ∃ P P' : Prop, (P → P') ∧
      uShape d r c i es = .leaf (PLift P) (.prop P) ∧ uShape d r' c i es = .leaf (PLift P') (.prop P')) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), FitsM uSig d r c i n e fs → FitsM uSig d r' c i n e fs
  | 0, _, _, _, hf => hf
  | n + 1, i, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fitsM_mono h n (i + 1) _ fs' h2⟩
    show FitsOneM uSig (uShape d r' c i e) f
    change FitsOneM uSig (uShape d r c i e) f at h1
    rcases h i e with he | ⟨P, P', hPP, hs, hs'⟩
    · rw [he]; exact h1
    · rw [hs] at h1
      rw [hs']
      obtain ⟨b, hb⟩ := h1
      exact ⟨⟨hPP b.down⟩, hb⟩

/-- **Membership is monotone in weaker proposition leaves** (`General.mono_prop`, proved; the parameter
relation `hle` is not used). -/
theorem mono_prop (dm : DataModel) (d : IndDecl) (ps ps' : List Sem)
    (hcanon : ∀ c i es, (uShape d (dm.recOf d ps') c i es = uShape d (dm.recOf d ps) c i es) ∨
      ∃ P P' : Prop, (P → P') ∧ uShape d (dm.recOf d ps) c i es = .leaf (PLift P) (.prop P) ∧
        uShape d (dm.recOf d ps') c i es = .leaf (PLift P') (.prop P'))
    (_hle : PropLe d ps ps') :
    (∃ v, dm.Mem d (dm.recOf d ps) v) → ∃ v, dm.Mem d (dm.recOf d ps') v := by
  rintro ⟨v, hv⟩
  obtain ⟨c, fs, rfl, hf⟩ := (DataLib.mem_iff uSig d _ v).1 hv
  exact ⟨_, (DataLib.mem_iff uSig d _ _).2 ⟨c, fs, rfl, fitsM_mono (hcanon c) _ 0 [] fs hf⟩⟩

end Ochr.Meaning.DataModel.Exists
