import Ochr.Meaning.Data
import Ochr.Meaning.Apply1

/-!
# The levels of the model's codes (what sort soundness reads of the model; docs/31 D77)

`sortOf_sound_stmt` (`Steps/Statements.lean`) says that a stored type's code has the level the
checker's `sortOf` reads of it. The facts of the model it consumes, on the data layer of docs/34,
kernel-checked here:

* the levels of the codes of `Nat`, `Unit`, a proposition, `Sort l` (its successor, `sortSucc`), a
  data type (its declaration's sort, `0` or `1`) and a Π-type (its declared sort);
* a member of `Sort l` is a code of level `l` (`mem_univ_level`);
* only a code of level `0` has `⋆` as a member, under the data model's reading
  (`proof_mem_level`): a data type's members are trees, never `⋆`.
-/

namespace Ochr.Meaning

theorem TyM.level_nat : TyM.nat.level = some 1 := rfl
theorem TyM.level_unit : TyM.unit.level = some 1 := rfl
theorem TyM.level_prop (P : Prop) : (TyM.prop P).level = some 0 := rfl

/-- `Sort l` is of sort `sortSucc l`, at the bounded levels. -/
theorem TyM.level_univ : ∀ l, l ≤ 2 → (TyM.univ l).level = some (sortSucc l)
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | _ + 3, h => absurd h (by omega)

/-- **A data type's code has its declaration's sort** (a declaration is in `Prop` or `Type₀`). -/
theorem DataModel.tyR_level (dm : DataModel) (d : IndDecl) (r : Rec) (hs : d.sort ≤ 1) :
    (dm.tyR d r).level = some d.sort := by
  unfold DataModel.tyR
  by_cases h0 : d.sort = 0
  · simp [h0]; rfl
  · have h1 : d.sort = 1 := by omega
    simp [h1]; rfl

theorem DataModel.tyM_level (dm : DataModel) (d : IndDecl) (ps : List Sem) (hs : d.sort ≤ 1) :
    (dm.tyM d ps).level = some d.sort :=
  DataModel.tyR_level dm d _ hs

/-- **A Π-type's code has its declared sort**, at the bounded levels. -/
theorem piTyAt_level (R : DataRead) (ds : List PiDom) (out : PiCod) :
    ∀ l, l ≤ 3 → (piTyAt R l ds out).level = some l
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | _ + 4, h => absurd h (by omega)

/-- **A member of `Sort l` is a code of level `l`**, at the bounded levels. -/
theorem mem_univ_level (R : DataRead) (s : Sem) :
    ∀ l, l ≤ 2 → s ∈ₛ[R] TyM.univ l → ∃ T, s = .ty T ∧ T.level = some l
  | 0, _, ⟨a, h⟩ => ⟨_, h.symm, rfl⟩
  | 1, _, ⟨a, h⟩ => ⟨_, h.symm, a.2.2⟩
  | 2, _, ⟨a, h⟩ => ⟨_, h.symm, a.2.2⟩
  | _ + 3, h, _ => absurd h (by omega)

/-- The data model's reading never gives `⋆`: an element reads as a member, a tree. -/
theorem DataModel.read_ne_proof (dm : DataModel) (d : IndDecl) (r : Rec) (A : Type) (a : A) :
    dm.read.read d r A a ≠ .proof := by
  show dm.readFn d r A a ≠ .proof
  unfold DataModel.readFn
  split
  · intro h
    have hm : dm.Mem d r .proof := (DataModel.mem_iff_meanC dm d r _).2 ⟨_, h⟩
    obtain ⟨_, _, he, _⟩ := (DataLib.mem_iff dm.sig d r _).1 hm
    cases he
  · intro h; cases h

theorem Code0.enc_proof_level (dm : DataModel) : ∀ {A : Type} (c : Code0 A) (a : A),
    c.enc dm.read a = .proof → c.level = some 0
  | _, .prop _, _, _ => rfl
  | _, .nat, _, h => by cases h
  | _, .unit, _, h => by cases h
  | _, .pi _ _, _, h => by cases h
  | _, .data d r A, a, h => absurd h (DataModel.read_ne_proof dm d r A a)
  | _, .err, a, _ => nomatch a

theorem Code1.enc_proof_level (dm : DataModel) : ∀ {A : Type 1} (c : Code1 A) (a : A),
    c.enc dm.read a = .proof → c.level = some 0
  | _, .lift _ c, a, h => Code0.enc_proof_level dm c a.down h
  | _, .univ0, _, h => by cases h
  | _, .univ1, _, h => by cases h
  | _, .pi _ _, _, h => by cases h

theorem Code2.enc_proof_level (dm : DataModel) : ∀ {A : Type 2} (c : Code2 A) (a : A),
    c.enc dm.read a = .proof → c.level = some 0
  | _, .lift _ c, a, h => Code1.enc_proof_level dm c a.down h
  | _, .univ2, _, h => by cases h
  | _, .pi _ _, _, h => by cases h

/-- **Only a code of level `0` has `⋆` as a member**, under the data model's reading. -/
theorem proof_mem_level (dm : DataModel) (T : TyM) (h : Sem.proof ∈ₛ[dm.read] T) : T.level = some 0 := by
  cases T with
  | t0 A c => obtain ⟨a, ha⟩ := h; exact Code0.enc_proof_level dm c a ha
  | t1 A c => obtain ⟨a, ha⟩ := h; exact Code1.enc_proof_level dm c a ha
  | t2 A c => obtain ⟨a, ha⟩ := h; exact Code2.enc_proof_level dm c a ha

end Ochr.Meaning

/-! ## What `PiFits` reads of the levels (the knot's split; `Steps.PiFits`, `Steps.PiCallable`) -/

namespace Ochr.Meaning

/-- **A canonical code whose level is at most `l` fits level `l`** (`1 ≤ l`): levels `0` and `1` are
carried at tier `0`, level `2` at tier `1`, level `3` at tier `2`. -/
theorem levelFit_of_level (T : TyM) (hc : T.Canon) {s l : Nat} (hs : T.level = some s) (hsl : s ≤ l)
    (hl : 1 ≤ l) : LevelFit l T := by
  cases T with
  | t0 A c => exact hl
  | t1 A c =>
    cases c with
    | lift => exact hc.elim
    | univ0 | univ1 | pi => simp [TyM.level, Code1.level] at hs; subst hs; exact hsl
  | t2 A c =>
    cases c with
    | lift => exact hc.elim
    | univ2 | pi => simp [TyM.level, Code2.level] at hs; subst hs; exact hsl

/-- **A canonical code of level `0` is a proposition.** -/
theorem prop_of_level_zero (T : TyM) (hc : T.Canon) (hs : T.level = some 0) : ∃ P, T = TyM.prop P := by
  cases T with
  | t0 A c =>
    cases c with
    | prop P => exact ⟨P, rfl⟩
    | _ => simp [TyM.level, Code0.level] at hs
  | t1 A c =>
    cases c with
    | lift => exact hc.elim
    | _ => simp [TyM.level, Code1.level] at hs
  | t2 A c =>
    cases c with
    | lift => exact hc.elim
    | _ => simp [TyM.level, Code2.level] at hs

/-- **A member of `Sort l` is a canonical code**, at the bounded levels: the universes' carriers hold
codes at their own level (`Sort 2`'s, level-1 codes of level `2`, never a lifted one). -/
theorem mem_univ_canon (R : DataRead) (s : Sem) :
    ∀ l, l ≤ 2 → s ∈ₛ[R] TyM.univ l → ∃ T, s = .ty T ∧ T.Canon
  | 0, _, ⟨a, h⟩ => ⟨_, h.symm, trivial⟩
  | 1, _, ⟨a, h⟩ => ⟨_, h.symm, trivial⟩
  | 2, _, ⟨⟨A, c, hc⟩, h⟩ => by
    refine ⟨_, h.symm, ?_⟩
    cases c with
    | lift B c' =>
      exfalso
      cases c' <;> simp [Code1.level, Code0.level] at hc
    | _ => trivial
  | _ + 3, h, _ => absurd h (by omega)

/-- **A Π-type's code has a level only at the bounded sorts** (`l ≤ 3`; above, `piTyAt` is `err`). -/
theorem le_three_of_piTyAt_level (R : DataRead) (ds : List PiDom) (out : PiCod) {l l' : Nat}
    (h : (piTyAt R l ds out).level = some l') : l ≤ 3 := by
  match l, h with
  | 0, _ => omega
  | 1, _ => omega
  | 2, _ => omega
  | 3, _ => omega
  | _ + 4, h => simp [piTyAt, TyM.level, TyM.err, Code0.level] at h

end Ochr.Meaning
