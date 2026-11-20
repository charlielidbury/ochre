import Ochr.Meaning.DataModel.Proto.Stages

/-!
# Prototype (b2): members, the carrier and its bijection

`Rz k d r v`: the meaning `v` is the meaning of an element of stage `k`. The members of `D` at
`r` (`Mem`) are the meanings some stage realizes; they are the least set closed under the
constructors (`mem_iff`). The carrier (`car`) holds each member once (at the stage equal to its
depth), and its meaning function (`meanC`) is a bijection onto the members.
-/

namespace Ochr.Meaning.DataModel.Proto

variable (S : Sig)

/-! ## Injectivity: a telescope is determined by its meanings -/

theorem tele_inj (L : Lvl) (hL : ∀ d r (x y : L.C d r), L.mean x = L.mean y → x = y)
    (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (t t' : Tele S L d r c i n e),
      Tele.mean S L i n e t = Tele.mean S L i n e t' → t = t'
  | _, 0, _, _, _, _ => rfl
  | i, n + 1, e, t, t', h => by
    have ih := fun v => tele_inj L hL d r c (i + 1) n (e ++ [Val.small v])
    revert t t'
    show ∀ (t t' : StepT L (S.shape d r c i e) (fun v => Tele S L d r c (i + 1) n (e ++ [v.small]))),
      StepT.mean L (fun v t' => Tele.mean S L (i + 1) n (e ++ [v.small]) t') _ t =
        StepT.mean L (fun v t' => Tele.mean S L (i + 1) n (e ++ [v.small]) t') _ t' → t = t'
    generalize S.shape d r c i e = s
    cases s with
    | leaf B cd =>
      rintro ⟨b, t⟩ ⟨b', t'⟩ h
      simp only [StepT.mean, List.cons.injEq] at h
      obtain rfl := encLeaf_inj cd h.1
      rw [ih _ t t' h.2]
    | sub d' r' =>
      rintro ⟨y, t⟩ ⟨y', t'⟩ h
      simp only [StepT.mean, List.cons.injEq] at h
      obtain rfl := hL d' r' y y' h.1
      rw [ih _ t t' h.2]

theorem lvl_inj : ∀ (k : Nat) (d : IndDecl) (r : Rec) (x y : (lvl S k).C d r),
    (lvl S k).mean x = (lvl S k).mean y → x = y
  | 0, _, _, x, _, _ => x.elim
  | k + 1, d, r, ⟨c, t⟩, ⟨c', t'⟩, h => by
    simp only [lvl, Val.dat.injEq, true_and] at h
    obtain ⟨hc, ht⟩ := h
    obtain rfl := Fin.ext hc
    rw [tele_inj S (lvl S k) (lvl_inj k) d r c 0 (arity d c) [] t t' ht]

/-! ## Realizability and its monotonicity -/

/-- `v` is the meaning of an element of stage `k` of `d` at `r`. -/
def Rz (k : Nat) (d : IndDecl) (r : Rec) (v : Val) : Prop := ∃ x : (lvl S k).C d r, (lvl S k).mean x = v

theorem fits_mono (L L' : Lvl) (h : ∀ d r f, FitsOne L (.sub d r) f → FitsOne L' (.sub d r) f)
    (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Val), Fits S L d r c i n e fs → Fits S L' d r c i n e fs
  | _, 0, _, _, hf => hf
  | i, n + 1, e, fs, ⟨f, fs', hfs, h1, h2⟩ => by
    refine ⟨f, fs', hfs, ?_, fits_mono L L' h d r c (i + 1) n _ fs' h2⟩
    revert h1
    generalize S.shape d r c i e = s
    cases s with
    | leaf _ _ => exact id
    | sub d' r' => exact h d' r' f

/-- Stage `k + 1` realizes exactly the constructor values whose fields fit at stage `k`. -/
theorem rz_succ_iff (k : Nat) (d : IndDecl) (r : Rec) (v : Val) :
    Rz S (k + 1) d r v ↔ ∃ c : Fin d.ctors.length, ∃ fs, v = .dat d.name r c fs ∧
      Fits S (lvl S k) d r c 0 (arity d c) [] fs := by
  constructor
  · rintro ⟨⟨c, t⟩, rfl⟩
    exact ⟨c, _, rfl, (tele_image S (lvl S k) d r c 0 _ [] _).1 ⟨t, rfl⟩⟩
  · rintro ⟨c, fs, rfl, hf⟩
    obtain ⟨t, ht⟩ := (tele_image S (lvl S k) d r c 0 _ [] fs).2 hf
    exact ⟨⟨c, t⟩, by simp only [lvl, ht]⟩

theorem rz_succ : ∀ (k : Nat) (d : IndDecl) (r : Rec) (v : Val), Rz S k d r v → Rz S (k + 1) d r v
  | 0, _, _, _, ⟨x, _⟩ => x.elim
  | k + 1, d, r, v, h => by
    obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 h
    exact (rz_succ_iff S (k + 1) d r _).2 ⟨c, fs, rfl,
      fits_mono S _ _ (fun d' r' f h => rz_succ k d' r' f h) d r c 0 _ [] fs hf⟩

theorem rz_le (k k' : Nat) (hk : k ≤ k') (d : IndDecl) (r : Rec) (v : Val) (h : Rz S k d r v) :
    Rz S k' d r v := by
  induction hk with
  | refl => exact h
  | step _ ih => exact rz_succ S _ d r v ih


theorem fits_mono_mem (L L' : Lvl) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Val),
      (∀ d' r' f, f ∈ fs → FitsOne L (.sub d' r') f → FitsOne L' (.sub d' r') f) →
      Fits S L d r c i n e fs → Fits S L' d r c i n e fs
  | _, 0, _, _, _, hf => hf
  | i, n + 1, e, fs, h, ⟨f, fs', hfs, h1, h2⟩ => by
    subst hfs
    refine ⟨f, fs', rfl, ?_, fits_mono_mem L L' d r c (i + 1) n _ fs'
      (fun d' r' g hg => h d' r' g (List.mem_cons_of_mem _ hg)) h2⟩
    revert h1
    generalize S.shape d r c i e = s
    cases s with
    | leaf _ _ => exact id
    | sub d' r' => exact h d' r' f (List.mem_cons_self ..)

theorem fits_mem (L : Lvl) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (i n : Nat) (e : List Small) (fs : List Val), Fits S L d r c i n e fs →
      ∀ f ∈ fs, (∃ (B : Type) (cd : Code B) (b : B), encLeaf cd b = f) ∨ ∃ d' r', FitsOne L (.sub d' r') f
  | _, 0, _, _, hf, f, hm => by simp only [Fits] at hf; subst hf; cases hm
  | i, n + 1, e, fs, ⟨g, fs', hfs, h1, h2⟩, f, hm => by
    subst hfs
    rcases List.mem_cons.1 hm with rfl | hm
    · revert h1
      generalize S.shape d r c i e = s
      cases s with
      | leaf B cd => exact fun ⟨b, hb⟩ => .inl ⟨B, cd, b, hb⟩
      | sub d' r' => exact fun h => .inr ⟨d', r', h⟩
    · exact fits_mem L d r c (i + 1) n _ fs' h2 f hm

/-- **A member is realized at the stage equal to its depth.** -/
theorem rz_depth : ∀ (k : Nat) (d : IndDecl) (r : Rec) (v : Val), Rz S k d r v → Rz S v.depth d r v
  | 0, _, _, _, ⟨x, _⟩ => x.elim
  | k + 1, d, r, v, h => by
    obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 h
    refine (rz_succ_iff S (Val.depthList fs) d r _).2 ⟨c, fs, rfl, ?_⟩
    refine fits_mono_mem S _ _ d r c 0 _ [] fs (fun d' r' f hm hf' => ?_) hf
    exact rz_le S _ _ (Val.depth_le_depthList fs f hm) d' r' f (rz_depth k d' r' f hf')

/-! ## The members -/

/-- **The members of `D` at `r`**: the meanings some stage realizes. -/
def Mem (d : IndDecl) (r : Rec) (v : Val) : Prop := ∃ k, Rz S k d r v

/-- A member is whole. -/
theorem rz_whole : ∀ (k : Nat) (d : IndDecl) (r : Rec) (v : Val), Rz S k d r v → v.whole
  | 0, _, _, _, ⟨x, _⟩ => x.elim
  | k + 1, d, r, v, h => by
    obtain ⟨c, fs, rfl, hf⟩ := (rz_succ_iff S k d r v).1 h
    simp only [Val.whole]
    intro f hm
    rcases fits_mem S _ d r c 0 _ [] fs hf f hm with ⟨B, cd, b, rfl⟩ | ⟨d', r', hf'⟩
    · exact encLeaf_whole cd b
    · exact rz_whole k d' r' f hf'

theorem mem_whole (d : IndDecl) (r : Rec) (v : Val) (h : Mem S d r v) : v.whole :=
  let ⟨k, hk⟩ := h; rz_whole S k d r v hk

/-! ## The carrier: each member once -/

/-- **The carrier of `D` at `r`**: the elements of the stage equal to their depth. -/
def car (d : IndDecl) (r : Rec) : Type :=
  Σ k : Nat, {x : (lvl S k).C d r // ((lvl S k).mean x).depth = k}

/-- **An element's meaning** (the reading). -/
def meanC {d : IndDecl} {r : Rec} (x : car S d r) : Val := (lvl S x.1).mean x.2.1

theorem meanC_inj {d : IndDecl} {r : Rec} (x y : car S d r) (h : meanC S x = meanC S y) : x = y := by
  obtain ⟨k, x, hx⟩ := x
  obtain ⟨k', y, hy⟩ := y
  simp only [meanC] at h
  have hk : k = k' := by rw [← hx, ← hy, h]
  subst hk
  obtain rfl := lvl_inj S k d r x y h
  rfl

/-- **The meanings of the carrier's elements are exactly the members.** -/
theorem mem_iff_meanC (d : IndDecl) (r : Rec) (v : Val) : Mem S d r v ↔ ∃ x : car S d r, meanC S x = v := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := rz_depth S k d r v hk
    exact ⟨⟨v.depth, x, by rw [hx]⟩, hx⟩
  · rintro ⟨⟨k, x, _⟩, rfl⟩
    exact ⟨k, x, rfl⟩

end Ochr.Meaning.DataModel.Proto
