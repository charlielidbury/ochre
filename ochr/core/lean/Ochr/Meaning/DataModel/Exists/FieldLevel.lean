import Ochr.Meaning.DataModel.Exists.LeafOk

/-!
# A field type runs to a level-0 code (exists11; docs/34 §18.16)

`FieldsFaithful` needs a field type's run, at members, to be a code of carrier level 0: the model's
field types are shape types, and the knot's field type is its meaning only at level 0
(`DeclStep.fieldsFaithful_spec`, `shapeTyP_uShape`). exists10 assumed it whole (`FieldLevels`). Here
it is PROVED (`fieldLevel0_of`) from the grammar's top shapes and two facts about the two shapes
whose value is not fixed by the grammar:
* a field type that is a parameter: the parameter's declared type is a sort `Prop` or `Type`
  (`hparam`; the checker's part, `Assembly.FieldHeads`); its members are then level-0 type values,
  by the parameter types' faithfulness;
* a field type that is a call of a global: every call through the global's meaning gives a level-0
  type value or no type value (`CallsLevel0`; the model's part, `Assembly.GlobalCallLevels`, from
  the checker's part that the global's stored codomain is `Prop` or `Type`).
`Nat`, `Unit`, an applied declaration and an equation run to level-0 codes by their top clauses.
-/

namespace Ochr.Meaning.DataModel.Exists.FieldLevel

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.DataModel.Exists.Knot Ochr.Meaning.DataModel.Exists.RunLemmas

/-- A value's reading as a type is a level-0 code: a level-0 type value, or no type value at all
(which reads as `err`). -/
def Lvl0V (v : Sem) : Prop := ∃ (B : Type) (cd : Code0 B), v.asTy = .t0 B cd

theorem lvl0V_of_not_ty {v : Sem} (h : ∀ X, v ≠ .ty X) : Lvl0V v := by
  cases v with
  | ty X => exact absurd rfl (h X)
  | _ => exact ⟨_, _, rfl⟩

theorem lvl0V_ty_t0 {B : Type} (cd : Code0 B) : Lvl0V (.ty (.t0 B cd)) := ⟨B, cd, rfl⟩

theorem enc0_lvl0 (dm : DataModel) {A : Type} (c : Code0 A) (a : A) : Lvl0V (c.enc dm.read a) :=
  lvl0V_of_not_ty fun X => LeafOk.enc0_ne_ty dm c a X

theorem enc1_lvl0 (dm : DataModel) : ∀ {A : Type 1} (c : Code1 A) (a : A), Lvl0V (c.enc dm.read a)
  | _, .lift _ c, a => enc0_lvl0 dm c a.down
  | _, .univ0, _ => ⟨_, _, rfl⟩
  | _, .univ1, _ => ⟨_, _, rfl⟩
  | _, .pi .., _ => lvl0V_of_not_ty fun _ h => by cases h

/-- **A function's calls give level-0 type values** (or no type value): what a call heading a field
type needs of the called global's meaning, at the model `dm`'s read. -/
def CallsLevel0 (dm : DataModel) (fv : Res) : Prop :=
  ∀ (args : List Res) (s : SState) (r : Res) (s' : SState), callOf dm.read fv args s = some (r, s') → Lvl0V r.1

/-- A function whose type is a level-0 or level-1 Π-type: its calls give level-0 type values. Only a
level-2 Π-type (a function into `Type₁`, or over a domain in `Type₁`) needs more. -/
theorem callsLevel0_of_not_t2 (dm : DataModel) (fv : Res)
    (h : ∀ (B : Type 2) (c : Code2 B), fv.2.m ≠ .t2 B c) : CallsLevel0 dm fv := by
  intro args s r s' hc
  unfold callOf at hc
  split at hc
  · obtain ⟨B, c, x, e⟩ := LeafOk.callOfL_enc _ _ _ _ _ hc
    rw [e]; exact enc0_lvl0 dm c x
  · obtain ⟨B, c, x, e⟩ := LeafOk.callOfL_enc _ _ _ _ _ hc
    rw [e]; exact enc1_lvl0 dm c x
  · rename_i hm
    exact absurd hm (h _ _)
  · cases hc

/-- The grammar's top shapes of a field type (`Knot.Spine`, `Knot.PSpine`). -/
inductive Top (d : IndDecl) : Term → Prop
  | nat : Top d .nat
  | unit : Top d .unit
  | param (v : Nat) (hv : v < d.params.length) : Top d (.place (.var v))
  | tind (n : String) (as : List Term) : Top d (.tind n as)
  | call (f : String) (as : List Term) (hd : Bool) : Top d (.call (.const f) as hd)
  | eq (A a b : Term) : Top d (.eq A a b)

theorem top_of_spine {Γ : List IndDecl} {d : IndDecl} {c : Nat} {FT : Term} (h : Spine Γ d c FT) : Top d FT := by
  cases h with
  | nat => exact .nat
  | unit => exact .unit
  | param v hv => exact .param v hv
  | tind n as => exact .tind n as
  | call f as hd => exact .call f as hd
  | eq A a b => exact .eq A a b

theorem top_of_pspine {Γ : List IndDecl} {d : IndDecl} {c : Nat} {FT : Term} (h : PSpine Γ d c FT) : Top d FT := by
  cases h with
  | nat => exact .nat
  | unit => exact .unit
  | param v hv => exact .param v hv
  | tind n as => exact .tind n as
  | call f as hd => exact .call f as hd
  | eq A a b => exact .eq A a b

/-- **A field type runs, at well-typed parameters and earlier fields, to a code of carrier level 0.** -/
def FieldLevel0 (K : RunCtx) (ρ : Assignment) (d : IndDecl) : Prop :=
  ∀ ps c i e FT r s', ps.length = d.params.length → ParamsTyped K.dm d ps → FieldsTyped K.dm d ps c e →
    e.length = i → fieldTerm d c i = some FT →
    run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D d ps c e) = some (r, s') →
    ∃ (B : Type) (cd : Code0 B), r.1.asTy = .t0 B cd

theorem paramsTyped_take {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : ParamsTyped dm d ps) (j : Nat) :
    ParamsTyped dm d (ps.take j) := fun j' hj' => by
  have hj'' : j' < ps.length := by simp at hj'; omega
  have := h j' hj''
  rw [List.getElem_take, List.take_take, Nat.min_eq_left (by simp at hj'; omega)]
  exact this

/-- **A field type runs to a level-0 code** (PROVED): from its top shape (`htop`, the grammar), a
parameter heading it declared at a sort `Prop` or `Type` (`hparam`), the globals heading one calling
to level-0 type values (`hcall`), and the parameter types' faithfulness (`hPF`). -/
theorem fieldLevel0_of (K : RunCtx) (ρ : Assignment) (d : IndDecl)
    (htop : ∀ c i FT, fieldTerm d c i = some FT → Top d FT)
    (hparam : ∀ c i v, fieldTerm d c i = some (.place (.var v)) → v < d.params.length →
      ∃ l, l ≤ 1 ∧ paramTerm d (d.params.length - 1 - v) = .sort l)
    (hcall : ∀ c i f as hd, fieldTerm d c i = some (.call (.const f) as hd) → CallsLevel0 K.dm (K.C.global f))
    (hPF : ParamsFaithfulAt K ρ d) : FieldLevel0 K ρ d := by
  intro ps c i e FT r s' hl hps he hei hFT hr
  change runT K ρ noFuture false _ FT _ = _ at hr
  change Lvl0V r.1
  cases htop c i FT hFT with
  | nat => rw [runT_nat] at hr; cases hr; exact ⟨_, _, rfl⟩
  | unit => simp only [runT, pure, Option.some.injEq] at hr; cases hr; exact ⟨_, _, rfl⟩
  | tind n as =>
    obtain ⟨M, psM, -, -, -, hr', -⟩ := runT_tind K ρ noFuture false _ n as _ hr
    rw [hr']
    show Lvl0V (.ty (K.dm.tyR M (K.dm.recOf M psM)))
    unfold DataModel.tyR
    split <;> exact ⟨_, _, rfl⟩
  | eq A a b =>
    obtain ⟨_, _, _, _, _, _, _, _, hr1, _⟩ := runT_eq K ρ noFuture false _ A a b _ hr
    rw [hr1]; exact ⟨_, _, rfl⟩
  | call f as hd =>
    obtain ⟨as', s₁, r', s₂, -, hc, hv⟩ := runT_call_const K ρ noFuture false _ f as hd _ hr
    rw [hv]; exact hcall c i f as hd hFT as' s₁ r' s₂ hc
  | param v hv =>
    have hj : ps.length - 1 - v < ps.length := by omega
    have hiA := fieldTerm_lt hFT
    have hr1 := runT_teleFrame_param K ρ noFuture false _ K.dm K.D d ps c e (by omega) (ps.length - 1 - v) hj
      (by omega) hr
    obtain ⟨l, hl1, hPT⟩ := hparam c i v hFT hv
    rw [← hl] at hPT
    have hjd : ps.length - 1 - v < d.params.length := by omega
    obtain ⟨p, hp⟩ : ∃ p, d.params[ps.length - 1 - v]? = some p := ⟨_, List.getElem?_eq_getElem hjd⟩
    have hp2 : p.2 = .sort l := by
      unfold paramTerm at hPT; rw [hp] at hPT; exact hPT
    have hpt : K.dm.paramTy d (ps.length - 1 - v) (ps.take (ps.length - 1 - v)) = TyM.univ l := by
      have := hPF (ps.take (ps.length - 1 - v)) (ps.length - 1 - v) p.1 (.sort l) (paramsTyped_take hps _)
        (by simp; omega) (by rw [hp, ← hp2]) _ _ (runT_sort K ρ noFuture false _ l _)
      exact this.symm
    have hm := hps (ps.length - 1 - v) hj
    rw [hpt] at hm
    rw [hr1]
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · obtain ⟨a, ha⟩ := hm; rw [← ha]; exact enc1_lvl0 K.dm _ a
    · obtain ⟨a, ha⟩ := hm; rw [← ha]; exact enc1_lvl0 K.dm _ a

end Ochr.Meaning.DataModel.Exists.FieldLevel
