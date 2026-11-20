import Ochr.Meaning.DataLib.Carrier

/-!
# The data model's library: the members are the least set closed under the constructors

`mem_iff`: a meaning is a member of `D` at `r` exactly when it is a constructor value of `D`
recording `r`, whose fields each fit their shape at the earlier ones, a data field being a member
of its own type. This is `DataModel`'s `pack_isSome`, `tag_pack`, `fields_pack` and `pack_fields`
in one statement, on meanings, with no reading.

A data type's meaning is its code `tyOf d r`: the declaration, the record, the carrier. Encoding a
carrier element is `meanC` (`encC`), membership is decoding (`memTy`), and the members of
`tyOf d r` are `Mem d r` (`memTy_tyOf`).
-/

namespace Ochr.Meaning.DataLib

variable (S : Sig)

/-- One field fits its shape among the members. -/
def FitsOneM : Shape → Sem → Prop
  | .leaf _ c, f => ∃ b, encLeaf c b = f
  | .sub d r, f => Mem S d r f
  | .prf d r, f => f = .proof ∧ ∃ v, Mem S d r v

/-- A telescope's meanings, each fitting its shape among the members. -/
def FitsM (d : IndDecl) (r : Rec) (c : Nat) : Nat → Nat → List Small → List Sem → Prop
  | _, 0, _, fs => fs = []
  | i, n + 1, e, fs => ∃ f fs', fs = f :: fs' ∧ FitsOneM S (S.shape d r c i e) f ∧
      FitsM d r c (i + 1) n (e ++ [f.small]) fs'

theorem fitsM_of_fits (k : Nat) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Sem), Fits S (lvl S k) d r c i n e fs → FitsM S d r c i n e fs
  | _, 0, _, _, hf => hf
  | i, n + 1, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fitsM_of_fits k d r c (i + 1) n _ fs' h2⟩
    revert h1
    generalize S.shape d r c i e = s
    cases s with
    | leaf _ _ => exact id
    | sub d' r' => exact fun h => ⟨k, h⟩
    | prf d' r' => exact fun ⟨hf, ⟨y⟩⟩ => ⟨hf, _, k, y, rfl⟩

theorem fits_of_fitsM (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Sem), FitsM S d r c i n e fs → ∃ k, Fits S (lvl S k) d r c i n e fs
  | _, 0, _, _, hf => ⟨0, hf⟩
  | i, n + 1, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    obtain ⟨K₁, hK₁⟩ := fits_of_fitsM d r c (i + 1) n _ fs' h2
    have h0 : ∃ k₀, FitsOne (lvl S k₀) (S.shape d r c i e) f := by
      revert h1
      generalize S.shape d r c i e = s
      cases s with
      | leaf _ _ => exact fun h => ⟨0, h⟩
      | sub d' r' => exact fun ⟨k, h⟩ => ⟨k, h⟩
      | prf d' r' => exact fun ⟨hf, _, k, y, _⟩ => ⟨k, hf, ⟨y⟩⟩
    obtain ⟨k₀, hk₀⟩ := h0
    refine ⟨max k₀ K₁, f, fs', hfs, ?_, fits_mono S _ _
      (fun d' r' g h => rz_le S K₁ _ (Nat.le_max_right _ _) d' r' g h) d r c (i + 1) n _ fs' hK₁⟩
    revert hk₀
    generalize S.shape d r c i e = s
    cases s with
    | leaf _ _ => exact id
    | sub d' r' => exact fun h => rz_le S k₀ _ (Nat.le_max_left _ _) d' r' f h
    | prf d' r' =>
      rintro ⟨hf, ⟨y⟩⟩
      obtain ⟨y', _⟩ := rz_le S k₀ _ (Nat.le_max_left _ _) d' r' _ ⟨y, rfl⟩
      exact ⟨hf, ⟨y'⟩⟩

/-- **The members are the least set closed under the constructors**: a member is a constructor
value of `D` recording `r` whose fields fit their shapes among the members, and every such value
is a member. -/
theorem mem_iff (d : IndDecl) (r : Rec) (v : Sem) :
    Mem S d r v ↔ ∃ c : Fin d.ctors.length, ∃ fs, v = .dat d.name r c fs ∧
      FitsM S d r c 0 (arity d c) [] fs := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => obtain ⟨x, _⟩ := hk; exact x.elim
    | succ k =>
      obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 hk
      exact ⟨c, fs, rfl, fitsM_of_fits S k d r c 0 _ [] fs hf⟩
  · rintro ⟨c, fs, rfl, hf⟩
    obtain ⟨k, hk⟩ := fits_of_fitsM S d r c 0 _ [] fs hf
    exact ⟨k + 1, (rz_succ_iff S k d r _).2 ⟨c, fs, rfl, hk⟩⟩

/-! ## A member is determined by its small reading

What makes records keyed by small readings lose nothing: two members of the same type with the
same constructor tree and leaves are the same meaning. So a later field's type, which the run
computes from the earlier fields' full meanings, is a function of their small readings on
well-typed fields. -/

theorem encLeaf_small_inj : ∀ {B : Type} (c : Code0 B) {a b : B}, (encLeaf c a).small = (encLeaf c b).small → a = b
  | _, .prop _, a, b, _ => by cases a; cases b; rfl
  | _, .nat, _, _, h => by simp only [encLeaf, Sem.small, Small.el.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .unit, a, b, _ => by cases a; cases b; rfl
  | _, .pi _ _, _, _, h => by simp only [encLeaf, Sem.small, Small.el.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .data _ _ _, _, _, h => by simp only [encLeaf, Sem.small, Small.el.injEq, heq_eq_eq, true_and] at h; exact h
  | _, .err, a, _, _ => nomatch a

theorem fits_small_inj (L : Lvl) (hL : ∀ d r f g, FitsOne L (.sub d r) f → FitsOne L (.sub d r) g → f.small = g.small → f = g)
    (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs gs : List Sem), Fits S L d r c i n e fs → Fits S L d r c i n e gs →
      Sem.smallList fs = Sem.smallList gs → fs = gs
  | _, 0, _, fs, gs, hf, hg, _ => by simp only [Fits] at hf hg; rw [hf, hg]
  | i, n + 1, e, fs, gs, ⟨f, fs', hfs, hf1, hf2⟩, ⟨g, gs', hgs, hg1, hg2⟩, hs => by
    subst hfs hgs
    simp only [Sem.smallList, List.cons.injEq] at hs
    have hfg : f = g := by
      revert hf1 hg1
      generalize S.shape d r c i e = s
      cases s with
      | leaf B cd =>
        rintro ⟨b, rfl⟩ ⟨b', rfl⟩
        rw [encLeaf_small_inj cd hs.1]
      | sub d' r' => exact fun h1 h2 => hL d' r' f g h1 h2 hs.1
      | prf d' r' => exact fun h1 h2 => h1.1.trans h2.1.symm
    subst hfg
    rw [fits_small_inj L hL d r c (i + 1) n _ fs' gs' hf2 hg2 hs.2]

theorem rz_small_inj : ∀ (k : Nat) (d : IndDecl) (r : Rec) (v w : Sem), Rz S k d r v → Rz S k d r w →
    v.small = w.small → v = w
  | 0, _, _, _, _, ⟨x, _⟩, _, _ => x.elim
  | k + 1, d, r, v, w, hv, hw, hs => by
    obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 hv
    obtain ⟨c', gs, rfl, hg⟩ := (rz_succ_iff S k d r w).1 hw
    simp only [Sem.small, Small.node.injEq] at hs
    obtain rfl := Fin.ext hs.1
    rw [fits_small_inj S (lvl S k) (fun d' r' f g h1 h2 h => rz_small_inj k d' r' f g h1 h2 h) d r c 0 _ [] fs gs
      hf hg hs.2]

/-- **Two members of one type with the same small reading are equal.** -/
theorem mem_small_inj (d : IndDecl) (r : Rec) (v w : Sem) (hv : Mem S d r v) (hw : Mem S d r w)
    (hs : v.small = w.small) : v = w := by
  obtain ⟨k, hk⟩ := hv
  obtain ⟨k', hk'⟩ := hw
  exact rz_small_inj S (max k k') d r v w (rz_le S k _ (Nat.le_max_left _ _) d r v hk)
    (rz_le S k' _ (Nat.le_max_right _ _) d r w hk') hs

end Ochr.Meaning.DataLib
