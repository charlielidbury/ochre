import Ochr.Meaning.DataModel.ParamSolve

/-!
# A constructor value built from member fields is a member (the run's constructor clause)

The second model fact of the type-soundness table (docs/31 D81): the run's constructor clause
(`Run.lean`'s `.ctor`, `ctorOut`) builds, at the record `r` it knows (from the written parameters,
the parameterless declaration, the hint, or the parameters solved from the fields), the tree
`ctorR d r c fs` typed at `tyR d r` (`•` at a `Prop`-sorted declaration). If each field is a member
of its field type at `r` and the earlier fields (`fieldTyR d r c i (fs.take i)`, what the clause runs
each field at once the record is known), the value is a member of that type.

* `mem_fitsOneM`: a member of a shape's type fits the shape (`fitsOneM_mem`'s converse).
* `ctorR_mem`: the tree is a member of `tyR d r` (a data declaration), from `DataLib.mem_iff`, at a
  record none of whose field shapes is a leaf holding a data code over the model's own carrier
  (`RecLeafOk`: canonical records, `RecordsFaithful.leafOk`; docs/34 §18).
* `ctorOut_mem`: the clause's result is a member of the type it gives it, both sorts.
-/

namespace Ochr.Meaning

open DataLib

namespace DataModel
variable (dm : DataModel)

/-- **A member of a shape's type fits the shape** (the converse of `fitsOneM_mem`; a non-canonical
shape's type, `err`, has no member). -/
theorem mem_fitsOneM (s : Shape) (f : Sem) (h : f ∈ₛ[dm.read] dm.shapeTy s) (hok : dm.LeafOk s) :
    DataLib.FitsOneM dm.sig s f := by
  cases s with
  | leaf B c =>
    cases c with
    | data d r A =>
      have hA : B ≠ dm.car d r := hok d r rfl
      obtain ⟨b, hb⟩ := h
      refine ⟨b, ?_⟩
      have : dm.readFn d r B b = f := hb
      simp only [readFn, dif_neg hA] at this
      exact this
    | err => obtain ⟨b, _⟩ := h; exact b.elim
    | prop P => obtain ⟨b, rfl⟩ := h; exact ⟨b, rfl⟩
    | nat => obtain ⟨b, rfl⟩ := h; exact ⟨b, rfl⟩
    | unit => obtain ⟨b, rfl⟩ := h; exact ⟨b, rfl⟩
    | pi C t => obtain ⟨b, rfl⟩ := h; exact ⟨b, rfl⟩
  | sub d r =>
    by_cases hs : (d.sort == 0) = true
    · exact absurd h (by simp only [shapeTy, hs, if_true]; exact err_mem_false dm.read f)
    · have hs' : (d.sort == 0) = false := by simpa using hs
      simp only [shapeTy, hs', Bool.false_eq_true, if_false] at h
      exact (dm.mem_tyR d r hs' f).1 h
  | prf d r =>
    by_cases hs : (d.sort == 0) = true
    · simp only [shapeTy, hs, if_true] at h
      rw [dm.tyR_prop d r hs] at h
      obtain ⟨⟨hv⟩, hf⟩ := h
      exact ⟨hf.symm, hv⟩
    · have hs' : (d.sort == 0) = false := by simpa using hs
      exact absurd h (by simp only [shapeTy, hs', Bool.false_eq_true, if_false]; exact err_mem_false dm.read f)

/-- Fields each a member of its field type at the earlier ones fit the telescope. -/
theorem fitsM_of_mem (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), fs.length = n →
      (∀ (j : Nat) (f : Sem), fs[j]? = some f →
        f ∈ₛ[dm.read] dm.shapeTy (dm.sig.shape d r c (i + j) (e ++ (fs.take j).map Sem.small))) →
      dm.RecLeafOk d r → DataLib.FitsM dm.sig d r c i n e fs
  | 0, _, _, fs, hl, _, _ => List.eq_nil_of_length_eq_zero hl
  | n + 1, i, e, [], hl, _, _ => by simp at hl
  | n + 1, i, e, f :: fs, hl, h, hok => by
    refine ⟨f, fs, rfl, dm.mem_fitsOneM _ f (by simpa using h 0 f rfl) (hok _ _ _), ?_⟩
    refine fitsM_of_mem d r c n (i + 1) (e ++ [f.small]) fs (by simpa using hl) (fun j g hg => ?_) hok
    have := h (j + 1) g (by simpa using hg)
    simpa [Nat.add_assoc, Nat.add_comm 1 j, List.take_succ_cons, List.append_assoc] using this

/-- **A constructor value built from member fields is a member** of its data type at the record. -/
theorem ctorR_mem (d : IndDecl) (r : Rec) (c : Nat) (fs : List Sem) (hs : (d.sort == 0) = false)
    (hc : c < d.ctors.length) (hl : fs.length = DataLib.arity d c)
    (hf : ∀ (i : Nat) (f : Sem), fs[i]? = some f → f ∈ₛ[dm.read] dm.fieldTyR d r c i (fs.take i))
    (hok : dm.RecLeafOk d r) :
    DataModel.ctorR d r c fs ∈ₛ[dm.read] dm.tyR d r := by
  rw [dm.mem_tyR d r hs]
  refine (DataLib.mem_iff dm.sig d r _).2 ⟨⟨c, hc⟩, fs, rfl, ?_⟩
  exact dm.fitsM_of_mem d r c _ 0 [] fs hl (fun j f hj => by simpa [fieldTyR] using hf j f hj) hok

/-- A `Prop`-sorted declaration: such a value witnesses its type, so `•` is a member. -/
theorem proof_mem_tyR (d : IndDecl) (r : Rec) (c : Nat) (fs : List Sem) (hs : (d.sort == 0) = true)
    (hc : c < d.ctors.length) (hl : fs.length = DataLib.arity d c)
    (hf : ∀ (i : Nat) (f : Sem), fs[i]? = some f → f ∈ₛ[dm.read] dm.fieldTyR d r c i (fs.take i))
    (hok : dm.RecLeafOk d r) :
    Sem.proof ∈ₛ[dm.read] dm.tyR d r := by
  rw [dm.tyR_prop d r hs]
  refine ⟨⟨⟨_, (DataLib.mem_iff dm.sig d r _).2 ⟨⟨c, hc⟩, fs, rfl, ?_⟩⟩⟩, rfl⟩
  exact dm.fitsM_of_mem d r c _ 0 [] fs hl (fun j f hj => by simpa [fieldTyR] using hf j f hj) hok

end DataModel

/-- **The constructor clause's result is a member of the type it gives it** (both sorts): at the
record the clause knows, from fields that are members of their field types at it. -/
theorem ctorOut_mem (dm : DataModel) (d : IndDecl) (r : Rec) (c : Nat) (fs : List Sem) (s : SState)
    (hc : c < d.ctors.length) (hl : fs.length = DataLib.arity d c)
    (hf : ∀ (i : Nat) (f : Sem), fs[i]? = some f → f ∈ₛ[dm.read] dm.fieldTyR d r c i (fs.take i))
    (hok : dm.RecLeafOk d r) :
    ∃ v T, ctorOut dm d c fs (some r) s = some ((v, T), s) ∧ T = .plain (dm.tyR d r) ∧ v ∈ₛ[dm.read] T.m := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  cases hs : (d.sort == 0)
  · simp only [hs, Bool.false_eq_true, if_false]
    exact dm.ctorR_mem d r c fs hs hc hl hf hok
  · simp only [hs, if_true]
    exact dm.proof_mem_tyR d r c fs hs hc hl hf hok

/-! ## Checks: `SW`'s and `SO`'s constructors, and a dependent constructor -/

namespace DataModel.CtorChecks
open DataModel.ParamSolve DataModel.Program

/-- `Wrap(3)`'s, `Opt2(3)`'s and `Single(Nat, 5)`'s records hold no leaf over a data code, so every
field shape at them is `LeafOk` (`ctorR_mem`'s side condition, docs/34 §18). -/
theorem wrap_leafOk : dmS.RecLeafOk wrapD (dmS.recOf wrapD [.el0 Nat 3]) :=
  recLeafOk_of dmS _ _ fun p B c hp => by
    change wrapRec (.el Nat 3) p = .leaf B c at hp
    unfold wrapRec at hp
    split at hp <;> (try (unfold tagRec at hp; split at hp)) <;> cases hp <;> rfl

theorem opt2_leafOk : dmS.RecLeafOk opt2D (dmS.recOf opt2D [.el0 Nat 3]) :=
  recLeafOk_of dmS _ _ fun p B c hp => by
    change opt2Rec (.el Nat 3) p = .leaf B c at hp
    unfold opt2Rec at hp
    split at hp <;> (try (unfold tagRec at hp; split at hp)) <;> cases hp <;> rfl

theorem single_leafOk : dmP.RecLeafOk singleD (dmP.recOf singleD [.ty TyM.nat, .el0 Nat 5]) :=
  recLeafOk_of dmP _ _ fun p B c hp => by
    change singleRec (.leaf Nat .nat) natRec (.el Nat 5) p = .leaf B c at hp
    unfold singleRec at hp
    split at hp <;> (try (unfold natRec at hp)) <;> cases hp <;> rfl

/-- **`SW`**: `MkW(t)` at `Wrap(3)` (the value `sw_ctor` builds) is a member of `Wrap(3)` when `t` is a
member of `Tag(3)`, the field's type at `Wrap(3)`'s record. -/
theorem sw_ctor_mem (tv : Sem) (htv : tv ∈ₛ[dmS.read] dmS.tyM tagD [.el0 Nat 3]) :
    dmS.ctorM wrapD [.el0 Nat 3] 0 [tv] ∈ₛ[dmS.read] dmS.tyM wrapD [.el0 Nat 3] :=
  dmS.ctorR_mem wrapD _ 0 [tv] rfl (by decide) rfl (fun i f hf => by
    match i, hf with
    | 0, hf => cases hf; exact htv
    | _ + 1, hf => simp at hf) wrap_leafOk

/-- **`SO`**: `A2(t)` at `Opt2(3)` (the value `so_ctor` builds) is a member of `Opt2(3)`. -/
theorem so_ctor_mem (tv : Sem) (htv : tv ∈ₛ[dmS.read] dmS.tyM tagD [.el0 Nat 3]) :
    dmS.ctorM opt2D [.el0 Nat 3] 0 [tv] ∈ₛ[dmS.read] dmS.tyM opt2D [.el0 Nat 3] :=
  dmS.ctorR_mem opt2D _ 0 [tv] rfl (by decide) rfl (fun i f hf => by
    match i, hf with
    | 0, hf => cases hf; exact htv
    | _ + 1, hf => simp at hf) opt2_leafOk

/-- **A dependent constructor**: `MkS(5, refl) : Single(Nat, 5)`, the second field's type the equation
`x = a` at the first field (read small). -/
theorem single_mem :
    dmP.ctorM singleD [.ty TyM.nat, .el0 Nat 5] 0 [.el0 Nat 5, .proof] ∈ₛ[dmP.read]
      dmP.tyM singleD [.ty TyM.nat, .el0 Nat 5] :=
  dmP.ctorR_mem singleD _ 0 _ rfl (by decide) rfl (fun i f hf => by
    match i, hf with
    | 0, hf => cases hf; exact ⟨5, rfl⟩
    | 1, hf => cases hf; exact ⟨⟨rfl⟩, rfl⟩
    | _ + 2, hf => simp at hf) single_leafOk

open Ochr.Meaning.Regress.CodeRuns

/-- **`SW` and `SO` run under the strict run** where `t` is a member of `Tag(3)`: the strict
constructor clause's membership test is `sw_ctor_mem`/`so_ctor_mem`. -/
theorem sw_runs_strict (ρ : Assignment) (φ : Future) (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole)
    (htv : tv ∈ₛ[dmS.read] dmS.tyM tagD [.el0 Nat 3]) (hint : TyS) :
    (run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "Wrap" 0 (hn "MkW") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv])).isSome :=
  ParamSolve.sw_runs ρ φ G tv hw (sw_ctor_mem tv htv) hint

theorem so_runs_strict (ρ : Assignment) (φ : Future) (G : String → Sem × TyS) (tv : Sem) (hw : tv.whole)
    (htv : tv ∈ₛ[dmS.read] dmS.tyM tagD [.el0 Nat 3]) (hint : TyS) :
    (run (Kp dmS ΓS G) ρ φ hint (.letIn (hn "w") (.ctor "Opt2" 0 (hn "A2") [] [.place (.var 0)]) (num 0))
      (frame [bindT (dmS.tyM tagD [.el0 Nat 3]) tv])).isSome :=
  ParamSolve.so_runs ρ φ G tv hw (so_ctor_mem tv htv) hint

end DataModel.CtorChecks

end Ochr.Meaning
