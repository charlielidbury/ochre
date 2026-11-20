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
