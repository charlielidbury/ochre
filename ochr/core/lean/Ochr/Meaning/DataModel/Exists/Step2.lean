import Ochr.Meaning.DataModel.Exists.PreludeModel
import Ochr.Test
import Ochr.Meaning.DataModel.Exists.Proto.Examples

/-!
# Step 2: the existence statement's conclusion at a program with the hard features (kernel-checked)

The program (after the library): `Bool`; `List (A : Type)`; `def EvT (b : Bool) : Type := match b
{ false => Nat, true => List(Nat) }`; `Rose (A : Type) := Node(a : A, kids : List(Rose(A)))`, nested
through `List`'s nestable parameter; `TF := MkTF(b : Bool, x : EvT(b))`, a field whose type is a
global type function of an earlier field; `Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) |
EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, m))`, a `Prop`-sorted declaration with a value parameter, a
non-uniform self-occurrence at an earlier field, an equation keyed by that field's small reading and a
proof field that is no index; `Q : Prop := MkQ(h : And(Q, True))`, a `Prop`-sorted declaration nested
at a `Prop` parameter (the case the knot cannot build, `PropNestCE.not_guarded`). Each as the checker
stores it (`step2_inds`, asserted natively).

The model `dmS fv`, given the meaning `fv` of the global `EvT`: the library's declarations as in
`PreludeModel`; `List` and `Rose` by the knot; `Ev` and `Q` TRUTH-FIRST (their own occurrences, and
`Q`'s inside `And`, read as the truth predicate's proposition, `evT` and `False`, then
`ev_tyR`/`q_tyR`: the record means the predicate); `TF`'s second field the type `EvT`'s meaning gives
at the first (`tfType`).

Proved, standard axioms: `RecordsFaithful`, `FieldsFaithful`, `ParamsFaithful`, `CtxFaithful` at every
run context with `dmS fv`, these declarations and `EvT` meaning `fv`, at every `fv` that gives a type
of `Type₀` (or does not run) at either `Bool` (`EvTGood`); `DataFaithful` at every program state
declaring the program; `instance_data` at the checker's decisions.

What this does NOT exercise, said plainly:
* `EvT`'s meaning as the RUN of its body: `instance_data_evt` takes `EvT` meaning a closure built by
  the model's own construction with the body's behaviour (`evtFv`; its call runs, `evtFv_call`, and
  `TF`'s second field is `List(Nat)` at `true`, `tfType_true`), not the meaning `defMeaning` computes
  from `EvT`'s term. That the latter satisfies `EvTGood` is the strict run's closure formation
  (membership of the function type) with `app_mem'` and the stored type's code being the closure's.
* the monotonicity induction of piece 5: `Q`'s truth is computed outright (`False`), as is `Ev`'s.
* an equation side calling a function (`S(S(m))` resolves to a call of a `λ`): `Ev` here is indexed by
  `Eq(Nat, n, m)`.
-/

namespace Ochr.Meaning.DataModel.Exists.Step2

open Ochr Ochr.Meaning Ochr.Meaning.DataLib Ochr.Meaning.Canonical Ochr.Meaning.DataModel.Exists.RunLemmas
open Ochr.Meaning.DataModel.Exists.PreludeModel

/-! ## The declarations, as the checker stores them -/

def boolD : IndDecl := { name := "Bool", sort := 1, ctors := [("false", []), ("true", [])] }
def listD : IndDecl :=
  { name := "List", params := [(hn "A", .sort 1)], sort := 1,
    ctors := [("Nil", []), ("Cons", [("h", .place (.var 0)), ("t", .tind "List" [.place (.var 0)])])],
    nestable := [true] }
def roseD : IndDecl :=
  { name := "Rose", params := [(hn "A", .sort 1)], sort := 1,
    ctors := [("Node", [("a", .place (.var 0)), ("kids", .tind "List" [.tind "Rose" [.place (.var 0)]])])],
    nestable := [true] }
def tfD : IndDecl :=
  { name := "TF", sort := 1,
    ctors := [("MkTF", [("b", .tind "Bool" []), ("x", .call (.const "EvT") [.place (.var 1)] false)])] }
def evD : IndDecl :=
  { name := "Ev", params := [(hn "n", .nat)], sort := 0,
    ctors := [("EvZ", [("h", .eq .nat (.place (.var 0)) .zero)]),
      ("EvSS", [("m", .nat), ("h", .tind "Ev" [.place (.var 3)]), ("e", .eq .nat (.place (.var 0)) (.place (.var 3)))])],
    nestable := [false] }
def qD : IndDecl :=
  { name := "Q", sort := 0, ctors := [("MkQ", [("h", .tind "And" [.tind "Q" [], .tind "True" []])])] }

def step2Decls : List IndDecl := preludeDecls ++ [boolD, listD, roseD, tfD, evD, qD]

open Ochr.Test in
ochr Step2A {
  inductive Bool := false | true
  inductive List (A : Type) := Nil | Cons(h : A, t : List(A))
  def EvT (b : Bool) : Type := (match b { false => Nat, true => List(Nat) })
  inductive Rose (A : Type) := Node(a : A, kids : List(Rose(A)))
  inductive TF := MkTF(b : Bool, x : EvT(b))
  inductive Ev (n : Nat) : Prop := EvZ(h : Eq(Nat, n, 0)) | EvSS(m : Nat, h : Ev(m), e : Eq(Nat, n, m))
  inductive Q : Prop := MkQ(h : And(Q, True))
}

open Ochr.Test in
-- every declaration of the block is accepted
#guard (Ochr.Test.run "Step2A" Step2A).rejectedWith []

/-- The block's items, after the library's, as `resolveDecl` makes them. -/
def step2Items : List Item :=
  (Prelude.decls ++ Step2A.decls).filterMap fun d => match Surface.resolveProgram (Prelude.decls ++ Step2A.decls) d with
    | .ok it => some it
    | .error _ => none

-- `step2_inds`: after the library and the block, the checker's inductive declarations are `step2Decls`
#guard let inds := (globalsAfter {} step2Items).2
  step2Items.length == 11 && inds.length == 10 && (inds.zip step2Decls).all fun ab => sameDecl ab.1 ab.2

/-! ## The knots and the truth predicates -/

/-- `List`: its tail at the declaration's own record function. -/
noncomputable def listK : KnotSpec where
  d := listD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 1 ∧ i = 0 then .ty (parTy ps 0) else if c = 1 ∧ i = 1 then .data listD (R ps)
    else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · exact data_agree _ (hR ps ps' hp)
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-- `Rose`: its forest a `List` at `Rose`'s own code, through `List`'s nestable parameter. -/
noncomputable def roseK : KnotSpec where
  d := roseD
  N := fun _ => true
  fty := fun R ps c i _ => if c = 0 ∧ i = 0 then .ty (parTy ps 0)
    else if c = 0 ∧ i = 1 then .data listD (recK listK [.ty (uTyR roseD (R ps))]) else .ty TyM.err
  pEntry := pEntryTy
  guarded := fun n R R' hR ps ps' hp c i es => by
    split
    · exact parTy_agree hp 0
    · split
      · exact data_agree _ (recK_agree listK n _ _
          (Proto.parAgree_single (Proto.semAgree_data roseD (by decide) (hR ps ps' hp))))
      · exact FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ hp j => pEntryTy_agree hp j

/-- One unfolding of `Ev`: `n = 0`, or `Ev(m)` with `n = m`. -/
def evF (S : List Sem → Prop) (ps : List Sem) : Prop :=
  Proto.parSem ps 0 = .el0 Nat 0 ∨ ∃ k : Nat, S [.el0 Nat k] ∧ Proto.parSem ps 0 = .el0 Nat k

/-- **`Ev`'s truth predicate**: the least predicate closed under its constructors. -/
def evT (ps : List Sem) : Prop := ∀ S : List Sem → Prop, (∀ ps', evF S ps' → S ps') → S ps

theorem evF_mono {S S' : List Sem → Prop} (h : ∀ ps, S ps → S' ps) (ps : List Sem) : evF S ps → evF S' ps
  | .inl h0 => .inl h0
  | .inr ⟨k, hk, he⟩ => .inr ⟨k, h _ hk, he⟩

theorem evT_closed (ps : List Sem) (h : evF evT ps) : evT ps :=
  fun S hS => hS ps (evF_mono (fun _ hT => hT S hS) ps h)

theorem evT_unfold (ps : List Sem) (h : evT ps) : evF evT ps :=
  h (evF evT) (fun ps' hps => evF_mono (fun ps'' => evT_closed ps'') ps' hps)

/-- `Ev`'s first earlier field, from the small readings. -/
def es0 (es : List Small) : Sem := ofSmall (es.getD 0 .other)

/-- `Ev`, truth-first: its own occurrence is a leaf holding the truth predicate; the value parameter
is kept small. -/
noncomputable def evK : KnotSpec where
  d := evD
  N := fun _ => false
  fty := fun _ ps c i es =>
    if c = 0 ∧ i = 0 then .ty (TyM.prop (Proto.parSem ps 0 = .el0 Nat 0))
    else if c = 1 ∧ i = 0 then .ty TyM.nat
    else if c = 1 ∧ i = 1 then .ty (TyM.prop (evT [es0 es]))
    else if c = 1 ∧ i = 2 then .ty (TyM.prop (Proto.parSem ps 0 = es0 es))
    else .ty TyM.err
  pEntry := fun ps j => .small (Proto.parSem ps j).small
  guarded := fun n R R' hR ps ps' hp c i es => by
    have h0 : Proto.parSem ps 0 = Proto.parSem ps' 0 := Proto.eq_parSem hp 0 rfl
    simp only [h0]
    exact FTyAgree.refl _ _
  pEntry_agree := fun _ ps ps' hp j => by
    have h0 : Proto.parSem ps j = Proto.parSem ps' j := Proto.eq_parSem hp j rfl
    simp only [h0]

/-- `True`'s record and `Q`'s truth: `Q` holds nowhere (`And(Q, True)` is least at `False`). -/
def emptyRec : Rec := fun _ => .none

/-- `Q`, truth-first: its field is `And` at `False` (its least truth) and `True`. -/
noncomputable def qK : KnotSpec where
  d := qD
  N := fun _ => false
  fty := fun _ _ c i _ => if c = 0 ∧ i = 0 then
      .data andD (recK (twoK andD) [.ty (TyM.prop False), .ty (uTyR trueD emptyRec)]) else .ty TyM.err
  pEntry := fun _ _ => .none
  guarded := fun _ _ _ _ _ _ _ _ _ _ => FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ _ _ => rfl

/-- A `Bool`, by its constructor. -/
def boolV (k : Nat) : Sem := .dat "Bool" emptyRec k []

/-- The `Bool` a small reading is (`false` unless it is `true`'s). -/
def boolOf (es : List Small) : Sem :=
  match es.getD 0 .other with
  | .node 1 _ => boolV 1
  | _ => boolV 0

/-- The reading every model has (the universal signature's). -/
noncomputable def uRead : DataRead := dmPre.read

/-- **What the global `EvT`, meaning `fv`, gives at a `Bool`**: the type its call returns (the error
type where the call does not run). A call's value depends on the callee and the argument values only
(`RunLemmas.callOf_val`), so any state and argument type will do. -/
noncomputable def tfType (fv : Res) (b : Sem) : TyM :=
  match callOf uRead fv [(b, .plain TyM.err)] (emptyState 0) with
  | some (r, _) => r.1.asTy
  | none => TyM.err

/-- `TF`: its first field a `Bool`, its second the type `EvT` gives at it. The record reads the
global's meaning: this is the coupling of the data model to the program's code (piece 3). -/
noncomputable def tfK (fv : Res) : KnotSpec where
  d := tfD
  N := fun _ => false
  fty := fun _ _ c i es => if c = 0 ∧ i = 0 then .data boolD emptyRec
    else if c = 0 ∧ i = 1 then .ty (tfType fv (boolOf es)) else .ty TyM.err
  pEntry := fun _ _ => .none
  guarded := fun _ _ _ _ _ _ _ _ _ _ => FTyAgree.refl _ _
  pEntry_agree := fun _ _ _ _ _ => rfl

/-- **The hypothesis on `EvT`'s meaning**: at either `Bool` it gives a type of `Type₀` or does not
run. The program meaning satisfies it because a global's meaning is built by the STRICT run (the
closure formation tests membership of the function type, `Run.lean`'s `.fix`), and applying a member
gives a member of the codomain (`app_mem'`); a meaning that does not run satisfies it vacuously. -/
def EvTGood (fv : Res) : Prop :=
  ∀ k < 2, (∃ (A : Type) (c : Code0 A), tfType fv (boolV k) = .t0 A c ∧ c.level = some 1) ∨ tfType fv (boolV k) = TyM.err

/-! ## The model -/

open Classical in
/-- **Step 2's data model**, given the meaning of the global type function `EvT`. -/
noncomputable def dmS (fv : Res) : DataModel where
  covers _ := True
  recOf d ps :=
    if d.name = "Pair" ∨ d.name = "And" then recK (twoK d) ps
    else if d.name = "List" then recK listK ps
    else if d.name = "Rose" then recK roseK ps
    else if d.name = "Ev" then recK evK ps
    else if d.name = "Q" then recK qK ps
    else if d.name = "TF" then recK (tfK fv) ps
    else emptyRec
  paramTy d _ _ :=
    if d.name = "Pair" ∨ d.name = "List" ∨ d.name = "Rose" then TyM.univ 1
    else if d.name = "And" then TyM.univ 0
    else if d.name = "Ev" then TyM.nat
    else TyM.err

variable {fv : Res}

theorem recOf_pair (ps : List Sem) : (dmS fv).recOf pairD ps = recK (twoK pairD) ps := by simp [dmS, pairD]
theorem recOf_and (ps : List Sem) : (dmS fv).recOf andD ps = recK (twoK andD) ps := by simp [dmS, andD]
theorem recOf_list (ps : List Sem) : (dmS fv).recOf listD ps = recK listK ps := by simp [dmS, listD]
theorem recOf_rose (ps : List Sem) : (dmS fv).recOf roseD ps = recK roseK ps := by simp [dmS, roseD]
theorem recOf_ev (ps : List Sem) : (dmS fv).recOf evD ps = recK evK ps := by simp [dmS, evD]
theorem recOf_q (ps : List Sem) : (dmS fv).recOf qD ps = recK qK ps := by simp [dmS, qD]
theorem recOf_bool (ps : List Sem) : (dmS fv).recOf boolD ps = emptyRec := by simp [dmS, boolD]
theorem recOf_false (ps : List Sem) : (dmS fv).recOf falseD ps = emptyRec := by simp [dmS, falseD]
theorem recOf_true (ps : List Sem) : (dmS fv).recOf trueD ps = emptyRec := by simp [dmS, trueD]
theorem recOf_tf (ps : List Sem) : (dmS fv).recOf tfD ps = recK (tfK fv) ps := by simp [dmS, tfD]

theorem paramTy_univ1 (d : IndDecl) (h : d = pairD ∨ d = listD ∨ d = roseD) (j : Nat) (ps : List Sem) :
    (dmS fv).paramTy d j ps = TyM.univ 1 := by
  rcases h with rfl | rfl | rfl <;> simp [dmS, pairD, listD, roseD]
theorem paramTy_and' (j : Nat) (ps : List Sem) : (dmS fv).paramTy andD j ps = TyM.univ 0 := by simp [dmS, andD]
theorem paramTy_ev (j : Nat) (ps : List Sem) : (dmS fv).paramTy evD j ps = TyM.nat := by simp [dmS, evD]
theorem paramTy_err (d : IndDecl) (h : d = boolD ∨ d = falseD ∨ d = trueD ∨ d = qD ∨ d = tfD) (j : Nat) (ps : List Sem) :
    (dmS fv).paramTy d j ps = TyM.err := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [dmS, boolD, falseD, trueD, qD, tfD]

/-! ## What the truth-first records mean -/

/-- A field whose type is a leaf code (not a data code) has that leaf as its shape. -/
theorem recK_shape_leaf (S : KnotSpec) (ps : List Sem) (c i : Nat) (es : List Small) (h : es.length = i)
    {B : Type} (cd : Code0 B) (hcd : cd.isData = false)
    (hF : S.fty (recK S) ps c i (projIdx S.d c es) = .ty (.t0 B cd)) :
    uShape S.d (recK S ps) c i es = .leaf B cd := by
  apply uShape_leaf
  rw [recK_kind S ps c i _ (by rw [projIdx_len, h]), hF]
  exact Proto.kind_nondata hcd

theorem evD_idx : evD.indexFields 1 = [0] := by decide

theorem projIdx_ev1 (sm : Small) : projIdx evD 1 [sm] = [sm] := by simp [projIdx, evD_idx]
theorem projIdx_ev2 (sm sh : Small) : projIdx evD 1 [sm, sh] = [sm, .other] := by simp [projIdx, evD_idx]

section
variable (n : Sem)

theorem ev_shape0 : uShape evD (recK evK [n]) 0 0 [] = .leaf _ (.prop (n = .el0 Nat 0)) :=
  recK_shape_leaf evK [n] 0 0 [] rfl _ rfl (by simp [evK, Proto.parSem, TyM.prop, TyM.nat] <;> rfl)

theorem ev_shape10 : uShape evD (recK evK [n]) 1 0 [] = .leaf Nat .nat :=
  recK_shape_leaf evK [n] 1 0 [] rfl _ rfl (by simp [evK, TyM.prop, TyM.nat] <;> rfl)

theorem ev_shape11 (sm : Small) : uShape evD (recK evK [n]) 1 1 [sm] = .leaf _ (.prop (evT [ofSmall sm])) :=
  recK_shape_leaf evK [n] 1 1 [sm] rfl _ rfl (by simp [evK, projIdx_ev1, es0, TyM.prop, TyM.nat] <;> rfl)

theorem ev_shape12 (sm sh : Small) :
    uShape evD (recK evK [n]) 1 2 [sm, sh] = .leaf _ (.prop (n = ofSmall sm)) :=
  recK_shape_leaf evK [n] 1 2 [sm, sh] rfl _ rfl
    (by simp [evK, projIdx_ev2, es0, Proto.parSem, TyM.prop, TyM.nat] <;> rfl)

theorem parSem_one : Proto.parSem [n] 0 = n := rfl

/-- **`Ev`'s carrier at its record is inhabited exactly when its truth predicate holds.** -/
theorem ev_mem_iff : (∃ v, DataLib.Mem uSig evD (recK evK [n]) v) ↔ evT [n] := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (DataLib.mem_iff uSig evD _ v).1 hv
    apply evT_closed
    match c, hc, hf with
    | 0, _, hf =>
      obtain ⟨f, _, rfl, h1, -⟩ := hf
      have h1' : FitsOneM uSig (uShape evD (recK evK [n]) 0 0 []) f := h1
      rw [ev_shape0] at h1'
      obtain ⟨⟨h⟩, -⟩ := h1'
      exact .inl h
    | 1, _, hf =>
      obtain ⟨f0, _, rfl, h0, f1, _, rfl, h1, f2, _, rfl, h2, -⟩ := hf
      have h0' : FitsOneM uSig (uShape evD (recK evK [n]) 1 0 []) f0 := h0
      rw [ev_shape10] at h0'
      obtain ⟨k, rfl⟩ := h0'
      have h1' : FitsOneM uSig (uShape evD (recK evK [n]) 1 1 [(Sem.el0 Nat k).small]) f1 := h1
      rw [ev_shape11] at h1'
      obtain ⟨⟨hk⟩, -⟩ := h1'
      have h2' : FitsOneM uSig (uShape evD (recK evK [n]) 1 2 [(Sem.el0 Nat k).small, f1.small]) f2 := h2
      rw [ev_shape12] at h2'
      obtain ⟨⟨he⟩, -⟩ := h2'
      exact .inr ⟨k, hk, by rw [parSem_one, he]; rfl⟩
    | k + 2, hc, _ => simp [evD] at hc; omega
  · intro hT
    rcases evT_unfold [n] hT with h0 | ⟨k, hk, he⟩
    · refine ⟨_, (DataLib.mem_iff uSig evD _ _).2 ⟨⟨0, by decide⟩, [.proof], rfl, .proof, [], rfl, ?_, rfl⟩⟩
      show FitsOneM uSig (uShape evD (recK evK [n]) 0 0 []) _
      rw [ev_shape0]
      exact ⟨⟨h0⟩, rfl⟩
    · refine ⟨_, (DataLib.mem_iff uSig evD _ _).2 ⟨⟨1, by decide⟩, [.el0 Nat k, .proof, .proof], rfl,
        .el0 Nat k, _, rfl, ?_, .proof, _, rfl, ?_, .proof, [], rfl, ?_, rfl⟩⟩
      · show FitsOneM uSig (uShape evD (recK evK [n]) 1 0 []) _
        rw [ev_shape10]; exact ⟨k, rfl⟩
      · show FitsOneM uSig (uShape evD (recK evK [n]) 1 1 [(Sem.el0 Nat k).small]) _
        rw [ev_shape11]; exact ⟨⟨hk⟩, rfl⟩
      · show FitsOneM uSig (uShape evD (recK evK [n]) 1 2 [(Sem.el0 Nat k).small, Sem.proof.small]) _
        rw [ev_shape12]
        exact ⟨⟨by rw [← parSem_one n, he]; rfl⟩, rfl⟩

/-- **`Ev(n)` means its truth predicate.** -/
theorem ev_tyR : uTyR evD (recK evK [n]) = TyM.prop (evT [n]) := by
  unfold uTyR
  rw [if_pos (by rfl)]
  congr 1
  apply propext
  refine Iff.trans ?_ (ev_mem_iff n)
  constructor
  · rintro ⟨x⟩; exact ⟨_, (DataLib.mem_iff_meanC uSig _ _ _).2 ⟨x, rfl⟩⟩
  · rintro ⟨v, hv⟩; obtain ⟨x, -⟩ := (DataLib.mem_iff_meanC uSig _ _ _).1 hv; exact ⟨x⟩

end

/-- `And`'s first field at a proposition is that proposition, a leaf. -/
theorem and_shape0 (P : Prop) (T : TyM) :
    uShape andD (recK (twoK andD) [.ty (TyM.prop P), .ty T]) 0 0 [] = .leaf (PLift P) (.prop P) :=
  recK_shape_leaf (twoK andD) _ 0 0 [] rfl _ rfl (by simp [twoK, parTy, Sem.asTy, TyM.prop] <;> rfl)

/-- `And` at `False` has no member. -/
theorem and_false_empty (T : TyM) (v : Sem) : ¬ DataLib.Mem uSig andD (recK (twoK andD) [.ty (TyM.prop False), .ty T]) v := by
  intro hv
  obtain ⟨⟨c, hc⟩, fs, -, hf⟩ := (DataLib.mem_iff uSig andD _ v).1 hv
  have hc0 : c = 0 := by simp [andD] at hc; omega
  subst hc0
  obtain ⟨f, _, -, h1, -⟩ := hf
  have h1' : FitsOneM uSig (uShape andD (recK (twoK andD) [.ty (TyM.prop False), .ty T]) 0 0 []) f := h1
  rw [and_shape0] at h1'
  obtain ⟨⟨h⟩, -⟩ := h1'
  exact h

/-- `Q`'s field at its record: a proof of `And` at `False` and `True`. -/
theorem q_shape : uShape qD (recK qK []) 0 0 [] = .prf andD (recK (twoK andD) [.ty (TyM.prop False), .ty (uTyR trueD emptyRec)]) := by
  have hk : recK qK [] (kindKey 0 0 (projIdx qD 0 [])) = .data andD := by
    rw [projIdx_nil, recK_kind qK [] 0 0 [] rfl]; rfl
  rw [uShape_data qD _ 0 0 [] andD hk]
  simp only [projIdx_nil]
  rw [recK_contRec qK [] 0 0 [] rfl]
  rfl

/-- **`Q` means `False`**: its least truth, which its record keeps. -/
theorem q_tyR : uTyR qD (recK qK []) = TyM.prop False := by
  unfold uTyR
  rw [if_pos (by rfl)]
  congr 1
  apply propext
  constructor
  · rintro ⟨x⟩
    obtain ⟨⟨c, hc⟩, fs, -, hf⟩ := (DataLib.mem_iff uSig qD _ _).1 ((DataLib.mem_iff_meanC uSig _ _ _).2 ⟨x, rfl⟩)
    have hc0 : c = 0 := by simp [qD] at hc; omega
    subst hc0
    obtain ⟨f, _, -, h1, -⟩ := hf
    have h1' : FitsOneM uSig (uShape qD (recK qK []) 0 0 []) f := h1
    rw [q_shape] at h1'
    obtain ⟨-, v, hv⟩ := h1'
    exact and_false_empty _ v hv
  · intro h; exact h.elim

/-! ## Generic: the leaves of a knot's record, and parameters by universe -/

/-- **A knot's record is `LeafOk` at its genuine keys** when each genuine field type is a data type
at a record or a code of level `0` or `1`. -/
theorem recLeafOk_recK (dm : DataModel) (S : KnotSpec) (ps : List Sem)
    (h : ∀ c i es, c < S.d.ctors.length → i < DataLib.arity S.d c → es.length = i →
      (∃ d' r', S.fty (recK S) ps c i es = .data d' r') ∨
      (∃ (A : Type) (cd : Code0 A), S.fty (recK S) ps c i es = .ty (.t0 A cd) ∧ (cd.level = some 1 ∨ cd.level = some 0))) :
    dm.RecLeafOk S.d (recK S ps) := by
  intro c i e hc hi he
  show dm.LeafOk (uShape S.d (recK S ps) c i e)
  have hpl : (projIdx S.d c e).length = i := by rw [projIdx_len, he]
  have hk := recK_kind S ps c i _ hpl
  rcases h c i (projIdx S.d c e) hc hi hpl with ⟨d', r', hF⟩ | ⟨A, cd, hF, hl⟩
  · rw [hF] at hk
    unfold uShape
    rw [hk]
    show dm.LeafOk (if d'.sort == 0 then _ else _)
    split <;> trivial
  · rw [hF] at hk
    exact leafOk_kind dm cd hl S.d (recK S ps) c i e hk

/-- A typed parameter at a parameter of type `Type₀` is a level-1 code; of type `Prop`, a
proposition; of type `Nat`, a number. -/
theorem typed_univ1 {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : ParamsTyped dm d ps) (j : Nat) (hj : j < ps.length)
    (hT : dm.paramTy d j (ps.take j) = TyM.univ 1) :
    ∃ (A : Type) (c : Code0 A), ps[j] = .ty (.t0 A c) ∧ c.level = some 1 := by
  have := h j hj; rw [hT] at this; exact mem_univ1 _ _ this

theorem typed_univ0 {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : ParamsTyped dm d ps) (j : Nat) (hj : j < ps.length)
    (hT : dm.paramTy d j (ps.take j) = TyM.univ 0) : ∃ P : Prop, ps[j] = .ty (TyM.prop P) := by
  have := h j hj; rw [hT] at this; exact mem_univ0 _ _ this

theorem typed_nat {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : ParamsTyped dm d ps) (j : Nat) (hj : j < ps.length)
    (hT : dm.paramTy d j (ps.take j) = TyM.nat) : ∃ k : Nat, ps[j] = .el0 Nat k := by
  have := h j hj; rw [hT] at this; obtain ⟨k, hk⟩ := this; exact ⟨k, hk.symm⟩

/-- A meaning whose small reading is a leaf's is that leaf. -/
theorem small_el {v : Sem} {A : Type} {a : A} (h : v.small = .el A a) : v = .el0 A a := by
  cases v <;> simp [Sem.small] at h
  obtain ⟨rfl, h⟩ := h
  cases h; rfl

theorem parTy_of {ps : List Sem} {j : Nat} {A : Type} {c : Code0 A} (hj : j < ps.length) (h : ps[j] = .ty (.t0 A c)) :
    parTy ps j = .t0 A c := by
  simp [parTy, List.getElem?_eq_getElem hj, h, Sem.asTy]

/-! ## `RecordsFaithful` -/

theorem mem_step2 {d : IndDecl} (h : d ∈ step2Decls) :
    d = pairD ∨ d = falseD ∨ d = trueD ∨ d = andD ∨ d = boolD ∨ d = listD ∨ d = roseD ∨ d = tfD ∨ d = evD ∨ d = qD := by
  simpa [step2Decls, preludeDecls] using h

theorem univ1_ne {A : Type} (c : Code0 A) : TyM.univ 1 ≠ .t0 A c := fun h => by cases h
theorem univ0_ne {A : Type} (c : Code0 A) : TyM.univ 0 ≠ .t0 A c := fun h => by cases h

/-- Typed parameter lists that agree but at value parameters with equal small readings are equal:
at this program a value parameter is a number, determined by its small reading. -/
theorem smallOnly_eq (d : IndDecl) (hd : d ∈ step2Decls) (ps ps' : List Sem) (hl : ps'.length = ps.length)
    (hps : ∀ (j : Nat) (v v' : Sem), ps[j]? = some v → ps'[j]? = some v' →
      v' = v ∨ ((∃ (A : Type) (c : Code0 A), (dmS fv).paramTy d j (ps.take j) = .t0 A c ∧ v ∈ₛ[(dmS fv).read] .t0 A c) ∧
        v'.small = v.small)) : ps' = ps := by
  apply List.ext_getElem?
  intro j
  rcases h1 : ps[j]? with _ | v
  · rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
  · rcases h2 : ps'[j]? with _ | v'
    · rw [List.getElem?_eq_none_iff] at h2
      obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.1 h1; omega
    · rcases hps j v v' h1 h2 with h | ⟨⟨A, c, hT, hv⟩, hs⟩
      · rw [h]
      · have hev : ∀ (A : Type) (c : Code0 A), (dmS fv).paramTy evD j (ps.take j) = .t0 A c → v ∈ₛ[(dmS fv).read] .t0 A c →
            v'.small = v.small → v' = v := by
          intro A c hT hv hs
          rw [paramTy_ev] at hT
          cases hT
          obtain ⟨k, hk⟩ := hv
          subst hk
          exact small_el hs
        rcases mem_step2 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hT (by rw [paramTy_univ1 _ (by simp) j]; exact univ1_ne c)
        · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
        · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
        · exact absurd hT (by rw [paramTy_and']; exact univ0_ne c)
        · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
        · exact absurd hT (by rw [paramTy_univ1 _ (by simp) j]; exact univ1_ne c)
        · exact absurd hT (by rw [paramTy_univ1 _ (by simp) j]; exact univ1_ne c)
        · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
        · rw [hev A c hT hv hs]
        · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)

/-- `boolOf` gives one of the two `Bool`s. -/
theorem boolOf_eq (es : List Small) : ∃ k < 2, boolOf es = boolV k := by
  unfold boolOf
  split
  · exact ⟨1, by omega, rfl⟩
  · exact ⟨0, by omega, rfl⟩

/-- **`TF`'s record is `LeafOk` at its genuine keys**: `Bool` is a data entry; `EvT`'s type, a level-1
code or the error type, by the hypothesis on its meaning. -/
theorem tf_leafOk (hfv : EvTGood fv) (ps : List Sem) : (dmS fv).RecLeafOk tfD ((dmS fv).recOf tfD ps) := by
  intro c i e hc hi he
  rw [recOf_tf]
  show (dmS fv).LeafOk (uShape tfD (recK (tfK fv) ps) c i e)
  have hc0 : c = 0 := by simp [tfD] at hc; omega
  subst hc0
  have hi2 : i < 2 := by simp [DataLib.arity, tfD] at hi; omega
  have hpl : (projIdx tfD 0 e).length = i := by rw [projIdx_len, he]
  have hk := recK_kind (tfK fv) ps 0 i _ hpl
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · unfold uShape
    rw [hk]
    show (dmS fv).LeafOk (if boolD.sort == 0 then _ else _)
    simp [boolD, DataModel.LeafOk]
  · obtain ⟨k, hk2, hb⟩ := boolOf_eq (projIdx tfD 0 e)
    have hfty : (tfK fv).fty (recK (tfK fv)) ps 0 1 (projIdx tfD 0 e) = .ty (tfType fv (boolV k)) := by
      simp [tfK, hb]
    rw [hfty] at hk
    rcases hfv k hk2 with ⟨A, cd, hT, hl⟩ | hT
    · rw [hT] at hk
      exact leafOk_kind _ cd (.inl hl) tfD _ 0 1 e hk
    · rw [hT] at hk
      have hkind : (FTy.ty TyM.err).kind = .leaf PEmpty .err := Proto.kind_nondata rfl
      unfold uShape
      rw [hk, hkind]
      intro d r h
      simp [Code0.dataCode?] at h

/-- **`RecordsFaithful` at step 2's program.** -/
theorem recordsFaithful (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (hfv : EvTGood fv) :
    RecordsFaithful K := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ
  subst hdm hΓ
  refine ⟨?types, ?values, ?smallOnly, ?leafOk⟩
  case types =>
    intro d hd ps j A c hlen hty _ hj
    rcases mem_step2 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [recOf_pair]; exact paramTyOf_recK _ _ rfl ps j c hj
    · simp [falseD] at hlen; subst hlen; simp at hj
    · simp [trueD] at hlen; subst hlen; simp at hj
    · rw [recOf_and]; exact paramTyOf_recK _ _ rfl ps j c hj
    · simp [boolD] at hlen; subst hlen; simp at hj
    · rw [recOf_list]; exact paramTyOf_recK _ _ rfl ps j c hj
    · rw [recOf_rose]; exact paramTyOf_recK _ _ rfl ps j c hj
    · simp [tfD] at hlen; subst hlen; simp at hj
    · rcases j with _ | j
      · simp [IndDecl.paramIsType, evD] at hty
      · simp [evD] at hlen; obtain ⟨hj', -⟩ := List.getElem?_eq_some_iff.1 hj; omega
    · simp [qD] at hlen; subst hlen; simp at hj
  case values =>
    intro d hd ps j v A c _ hj hT hv
    rcases mem_step2 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hT (by rw [paramTy_univ1 _ (by simp) j]; exact univ1_ne c)
    · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
    · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
    · exact absurd hT (by rw [paramTy_and']; exact univ0_ne c)
    · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
    · exact absurd hT (by rw [paramTy_univ1 _ (by simp) j]; exact univ1_ne c)
    · exact absurd hT (by rw [paramTy_univ1 _ (by simp) j]; exact univ1_ne c)
    · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
    · rw [recOf_ev, recK_param]
      simp [evK, Proto.parSem, List.getD_eq_getElem?_getD, hj]
    · rw [paramTy_err _ (by simp) j] at hT; cases hT; exact absurd hv (DataModel.err_mem_false _ _)
  case smallOnly =>
    intro d hd ps ps' _ hl hps
    rw [smallOnly_eq d hd ps ps' hl hps]
  case leafOk =>
    intro d hd ps hlen hpt
    rcases mem_step2 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [recOf_pair]
      refine recLeafOk_recK _ (twoK pairD) ps fun c i es hc hi _ => .inr ?_
      have hc0 : c = 0 := by simp [twoK, pairD] at hc; omega
      have hi2 : i < 2 := by simp [twoK, DataLib.arity, pairD, hc0] at hi; omega
      have hpl : ps.length = 2 := by simpa [pairD] using hlen
      obtain ⟨A, cd, hA, hlv⟩ := typed_univ1 hpt i (by omega) (paramTy_univ1 _ (by simp) i _)
      refine ⟨A, cd, ?_, .inl hlv⟩
      subst hc0
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [twoK, parTy_of (by omega) hA]
    · intro c i e hc; simp [falseD] at hc
    · intro c i e hc hi; simp [trueD] at hc; subst hc; simp [DataLib.arity, trueD] at hi
    · rw [recOf_and]
      refine recLeafOk_recK _ (twoK andD) ps fun c i es hc hi _ => .inr ?_
      have hc0 : c = 0 := by simp [twoK, andD] at hc; omega
      have hi2 : i < 2 := by simp [twoK, DataLib.arity, andD, hc0] at hi; omega
      have hpl : ps.length = 2 := by simpa [andD] using hlen
      obtain ⟨P, hP⟩ := typed_univ0 hpt i (by omega) (paramTy_and' i _)
      refine ⟨PLift P, .prop P, ?_, .inr rfl⟩
      subst hc0
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [twoK, parTy_of (by omega) hP, TyM.prop]
    · intro c i e hc hi; simp [boolD] at hc
      rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> simp [DataLib.arity, boolD] at hi
    · rw [recOf_list]
      refine recLeafOk_recK _ listK ps fun c i es hc hi _ => ?_
      have hpl : ps.length = 1 := by simpa [listD] using hlen
      rcases (show c = 0 ∨ c = 1 by simp [listK, listD] at hc; omega) with rfl | rfl
      · simp [listK, DataLib.arity, listD] at hi
      · rcases (show i = 0 ∨ i = 1 by simp [listK, DataLib.arity, listD] at hi; omega) with rfl | rfl
        · obtain ⟨A, cd, hA, hlv⟩ := typed_univ1 hpt 0 (by omega) (paramTy_univ1 _ (by simp) 0 _)
          exact .inr ⟨A, cd, by simp [listK, parTy_of (by omega) hA], .inl hlv⟩
        · exact .inl ⟨listD, recK listK ps, by simp [listK]⟩
    · rw [recOf_rose]
      refine recLeafOk_recK _ roseK ps fun c i es hc hi _ => ?_
      have hpl : ps.length = 1 := by simpa [roseD] using hlen
      have hc0 : c = 0 := by simp [roseK, roseD] at hc; omega
      subst hc0
      rcases (show i = 0 ∨ i = 1 by simp [roseK, DataLib.arity, roseD] at hi; omega) with rfl | rfl
      · obtain ⟨A, cd, hA, hlv⟩ := typed_univ1 hpt 0 (by omega) (paramTy_univ1 _ (by simp) 0 _)
        have hp0 := parTy_of (show 0 < ps.length by omega) hA
        exact .inr ⟨A, cd, by simp [roseK, hp0], .inl hlv⟩
      · exact .inl ⟨listD, recK listK [.ty (uTyR roseD (recK roseK ps))], rfl⟩
    · exact tf_leafOk hfv ps
    · rw [recOf_ev]
      refine recLeafOk_recK _ evK ps fun c i es hc hi _ => .inr ?_
      rcases (show c = 0 ∨ c = 1 by simp [evK, evD] at hc; omega) with rfl | rfl
      · have hi0 : i = 0 := by simp [evK, DataLib.arity, evD] at hi; omega
        subst hi0
        exact ⟨_, .prop (Proto.parSem ps 0 = .el0 Nat 0), rfl, .inr rfl⟩
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 by simp [evK, DataLib.arity, evD] at hi; omega) with rfl | rfl | rfl
        · exact ⟨Nat, .nat, rfl, .inl rfl⟩
        · exact ⟨_, .prop (evT [es0 es]), rfl, .inr rfl⟩
        · exact ⟨_, .prop (Proto.parSem ps 0 = es0 es), rfl, .inr rfl⟩
    · rw [recOf_q]
      refine recLeafOk_recK _ qK ps fun c i es hc hi _ => .inl ?_
      have hc0 : c = 0 := by simp [qK, qD] at hc; omega
      have hi0 : i = 0 := by simp [qK, DataLib.arity, qD, hc0] at hi; omega
      subst hc0 hi0
      exact ⟨andD, _, rfl⟩

/-! ## `FieldsFaithful` -/

/-- A knot's field type, read off its record (any model whose record for the declaration is the knot's). -/
theorem fieldTy_knot (dm : DataModel) (S : KnotSpec) (d : IndDecl) (hSd : S.d = d) (ps : List Sem)
    (hrec : dm.recOf d ps = recK S ps) (c i : Nat) (e : List Sem) (he : e.length = i)
    (hL : (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).Lvl0) :
    dm.fieldTy d ps c i e = (S.fty (recK S) ps c i (projIdx d c (e.map Sem.small))).mean := by
  subst hSd
  unfold DataModel.fieldTy DataModel.fieldTyR
  rw [hrec, shapeTy_eq_shapeTyP]
  exact recK_shape S ps c i _ (by simp [he]) hL

theorem find_list : step2Decls.find? (·.name == "List") = some listD := rfl
theorem find_rose : step2Decls.find? (·.name == "Rose") = some roseD := rfl
theorem find_ev : step2Decls.find? (·.name == "Ev") = some evD := rfl
theorem find_q : step2Decls.find? (·.name == "Q") = some qD := rfl
theorem find_and : step2Decls.find? (·.name == "And") = some andD := rfl
theorem find_true : step2Decls.find? (·.name == "True") = some trueD := rfl

theorem tyM_list (ps : List Sem) : (dmS fv).tyM listD ps = uTyR listD (recK listK ps) := by
  unfold DataModel.tyM; rw [recOf_list]; rfl
theorem tyM_rose (ps : List Sem) : (dmS fv).tyM roseD ps = uTyR roseD (recK roseK ps) := by
  unfold DataModel.tyM; rw [recOf_rose]; rfl
theorem tyM_ev (ps : List Sem) : (dmS fv).tyM evD ps = uTyR evD (recK evK ps) := by
  unfold DataModel.tyM; rw [recOf_ev]; rfl
theorem tyM_q : (dmS fv).tyM qD [] = TyM.prop False := by
  unfold DataModel.tyM; rw [recOf_q]; exact q_tyR
theorem tyM_true : (dmS fv).tyM trueD [] = uTyR trueD emptyRec := by
  unfold DataModel.tyM; rw [recOf_true]; rfl
theorem tyM_and (ps : List Sem) : (dmS fv).tyM andD ps = uTyR andD (recK (twoK andD) ps) := by
  unfold DataModel.tyM; rw [recOf_and]; rfl

theorem list_one {ps : List Sem} (h : ps.length = 1) : ps = [ps[0]] := by
  rcases ps with _ | ⟨a, _ | _⟩ <;> simp at h ⊢

theorem two_list {ps : List Sem} (h : ps.length = 2) : ps = [ps[0], ps[1]] := by
  rcases ps with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at h ⊢

/-- `List`'s field types are the run's. -/
theorem fields_list (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (ρ : Assignment)
    (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (hlen : ps.length = 1)
    (hpt : ParamsTyped (dmS fv) listD ps) (he : e.length = i) (hFT : fieldTerm listD c i = some FT)
    {r : Res} {s' : SState} (hr : run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D listD ps c e) = some (r, s')) :
    r.1.asTy = (dmS fv).fieldTy listD ps c i e := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hr
  subst hdm hΓ
  unfold run at hr
  obtain ⟨A, cd, hA, -⟩ := typed_univ1 hpt 0 (by omega) (paramTy_univ1 _ (by simp) 0 _)
  have hp0 := parTy_of (show 0 < ps.length by omega) hA
  have hc : c = 1 ∧ (i = 0 ∧ FT = .place (.var 0) ∨ i = 1 ∧ FT = .tind "List" [.place (.var 0)]) := by
    rcases c with _ | _ | c <;> rcases i with _ | _ | i <;> simp [fieldTerm, listD] at hFT <;> simp [hFT]
  have hvar : (0 : Nat) = ps.length - 1 - 0 := by omega
  have har : e.length ≤ DataLib.arity listD 1 := by simp [DataLib.arity, listD]; omega
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hc
  · have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D listD ps 1 e har 0 (by omega) hvar hr
    rw [h1, fieldTy_knot (dmS fv) listK listD rfl ps (recOf_list ps) 1 0 e he (by simp [listK, hp0, FTy.Lvl0])]
    simp [listK, hp0, FTy.mean, hA, Sem.asTy]
  · obtain ⟨d, v, T, s₁, hd, hv, hr1⟩ := runT_tind1 _ ρ noFuture false _ "List" _ _ hr
    have hdd : d = listD := by dsimp only at hd; rw [find_list] at hd; exact (Option.some.inj hd).symm
    subst hdd
    have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D listD ps 1 e har 0 (by omega) hvar hv
    simp only at h1
    rw [hr1, h1, fieldTy_knot (dmS fv) listK listD rfl ps (recOf_list ps) 1 1 e he (by simp [listK, FTy.Lvl0])]
    dsimp only
    rw [tyM_list, ← list_one hlen]
    simp [listK, FTy.mean, Sem.asTy]

/-- `Rose`'s field types are the run's: its forest is `List` at `Rose`'s own code. -/
theorem fields_rose (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (ρ : Assignment)
    (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (hlen : ps.length = 1)
    (hpt : ParamsTyped (dmS fv) roseD ps) (he : e.length = i) (hFT : fieldTerm roseD c i = some FT)
    {r : Res} {s' : SState} (hr : run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D roseD ps c e) = some (r, s')) :
    r.1.asTy = (dmS fv).fieldTy roseD ps c i e := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hr
  subst hdm hΓ
  unfold run at hr
  obtain ⟨A, cd, hA, -⟩ := typed_univ1 hpt 0 (by omega) (paramTy_univ1 _ (by simp) 0 _)
  have hp0 := parTy_of (show 0 < ps.length by omega) hA
  have hc : c = 0 ∧ (i = 0 ∧ FT = .place (.var 0) ∨ i = 1 ∧ FT = .tind "List" [.tind "Rose" [.place (.var 0)]]) := by
    rcases c with _ | c <;> rcases i with _ | _ | i <;> simp [fieldTerm, roseD] at hFT <;> simp [hFT]
  have hvar : (0 : Nat) = ps.length - 1 - 0 := by omega
  have har : e.length ≤ DataLib.arity roseD 0 := by simp [DataLib.arity, roseD]; omega
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hc
  · have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D roseD ps 0 e har 0 (by omega) hvar hr
    rw [h1, fieldTy_knot (dmS fv) roseK roseD rfl ps (recOf_rose ps) 0 0 e he (by simp [roseK, hp0, FTy.Lvl0])]
    simp [roseK, hp0, FTy.mean, hA, Sem.asTy]
  · obtain ⟨d, v, T, s₁, hd, hv, hr1⟩ := runT_tind1 _ ρ noFuture false _ "List" _ _ hr
    have hdd : d = listD := by dsimp only at hd; rw [find_list] at hd; exact (Option.some.inj hd).symm
    subst hdd
    obtain ⟨d', w, U, s₂, hd', hw, hv1⟩ := runT_tind1 _ ρ noFuture false _ "Rose" _ _ hv
    have hdd' : d' = roseD := by dsimp only at hd'; rw [find_rose] at hd'; exact (Option.some.inj hd').symm
    subst hdd'
    have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D roseD ps 0 e har 0 (by omega) hvar hw
    simp only at h1 hv1
    rw [hr1, hv1, h1, fieldTy_knot (dmS fv) roseK roseD rfl ps (recOf_rose ps) 0 1 e he (by simp [roseK, FTy.Lvl0])]
    dsimp only
    rw [tyM_list, tyM_rose, ← list_one hlen]
    simp [roseK, FTy.mean, Sem.asTy]

/-- `Ev`'s field types are the run's: the equations at the parameter and the first field, the
self-occurrence at its truth predicate (`ev_tyR`). -/
theorem fields_ev (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (ρ : Assignment)
    (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (hlen : ps.length = 1)
    (hft : FieldsTyped (dmS fv) evD ps c e) (he : e.length = i) (hFT : fieldTerm evD c i = some FT)
    {r : Res} {s' : SState} (hr : run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D evD ps c e) = some (r, s')) :
    r.1.asTy = (dmS fv).fieldTy evD ps c i e := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hr
  subst hdm hΓ
  unfold run at hr
  have hps : ps = [ps[0]] := list_one hlen
  have hc : (c = 0 ∧ i = 0 ∧ FT = .eq .nat (.place (.var 0)) .zero) ∨ (c = 1 ∧ i = 0 ∧ FT = .nat) ∨
      (c = 1 ∧ i = 1 ∧ FT = .tind "Ev" [.place (.var 3)]) ∨
      (c = 1 ∧ i = 2 ∧ FT = .eq .nat (.place (.var 0)) (.place (.var 3))) := by
    rcases c with _ | _ | c <;> rcases i with _ | _ | _ | i <;> simp [fieldTerm, evD] at hFT <;> simp [hFT]
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- `h : Eq(Nat, n, 0)`
    obtain ⟨TA, va, vb, s₁, ⟨RA, hA⟩, ⟨Ra, sa, ha⟩, ⟨Rb, sb, hb⟩, -, hr1, -⟩ := runT_eq _ ρ noFuture false _ _ _ _ _ hr
    rw [runT_nat] at hA
    simp only [Option.some.injEq, Prod.mk.injEq] at hA
    obtain ⟨⟨rfl, -⟩, rfl⟩ := hA
    rw [runT_zero] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨⟨rfl, -⟩, -⟩ := hb
    have har : e.length ≤ DataLib.arity evD 0 := by simp [DataLib.arity, evD]; omega
    have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D evD ps 0 e har 0 (by omega) (by omega) ha
    simp only at h1
    rw [hr1, h1, fieldTy_knot (dmS fv) evK evD rfl ps (recOf_ev ps) 0 0 e he (by simp [evK, FTy.Lvl0, TyM.prop])]
    simp [evK, FTy.mean, Sem.asTy, Proto.parSem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 0 < ps.length by omega)]
  · -- `m : Nat`
    rw [runT_nat] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    rw [fieldTy_knot (dmS fv) evK evD rfl ps (recOf_ev ps) 1 0 e he (by simp [evK, FTy.Lvl0, TyM.nat])]
    simp [evK, FTy.mean, Sem.asTy]
  · -- `h : Ev(m)`
    obtain ⟨d, v, T, s₁, hd, hv, hr1⟩ := runT_tind1 _ ρ noFuture false _ "Ev" _ _ hr
    have hdd : d = evD := by dsimp only at hd; rw [find_ev] at hd; exact (Option.some.inj hd).symm
    subst hdd
    have har : e.length ≤ DataLib.arity evD 1 := by simp [DataLib.arity, evD]; omega
    have hvar : (3 : Nat) = DataLib.arity evD 1 + ps.length - 1 - 0 := by simp [DataLib.arity, evD, hlen]
    have h1 := runT_teleFrame_field _ ρ noFuture false _ (dmS fv) D evD ps 1 e har 0 (by omega) hvar hv
    simp only at h1
    -- the first field is a number
    have hm := hft 0 (by omega)
    rw [fieldTy_knot (dmS fv) evK evD rfl ps (recOf_ev ps) 1 0 _ (by simp) (by simp [evK, FTy.Lvl0, TyM.nat])] at hm
    simp [evK, FTy.mean] at hm
    obtain ⟨k, hk⟩ := hm
    rw [hr1, h1, fieldTy_knot (dmS fv) evK evD rfl ps (recOf_ev ps) 1 1 e he (by simp [evK, FTy.Lvl0, TyM.prop])]
    dsimp only
    rw [tyM_ev, ev_tyR]
    obtain ⟨e0, rfl⟩ : ∃ e0, e = [e0] := by
      rcases e with _ | ⟨a, _ | _⟩ <;> simp at he
      exact ⟨a, rfl⟩
    simp at hk
    subst hk
    simp [evK, FTy.mean, Sem.asTy, es0, projIdx_ev1]
    rfl
  · -- `e : Eq(Nat, n, m)`
    obtain ⟨TA, va, vb, s₁, ⟨RA, hA⟩, ⟨Ra, sa, ha⟩, ⟨Rb, sb, hb⟩, -, hr1, -⟩ := runT_eq _ ρ noFuture false _ _ _ _ _ hr
    rw [runT_nat] at hA
    simp only [Option.some.injEq, Prod.mk.injEq] at hA
    obtain ⟨⟨rfl, -⟩, rfl⟩ := hA
    have har : e.length ≤ DataLib.arity evD 1 := by simp [DataLib.arity, evD]; omega
    have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D evD ps 1 e har 0 (by omega) (by omega) ha
    have hvar : (3 : Nat) = DataLib.arity evD 1 + ps.length - 1 - 0 := by simp [DataLib.arity, evD, hlen]
    have h2 := runT_teleFrame_field _ ρ noFuture false _ (dmS fv) D evD ps 1 e har 0 (by omega) hvar hb
    simp only at h1 h2
    have hm := hft 0 (by omega)
    rw [fieldTy_knot (dmS fv) evK evD rfl ps (recOf_ev ps) 1 0 _ (by simp) (by simp [evK, FTy.Lvl0, TyM.nat])] at hm
    simp [evK, FTy.mean] at hm
    obtain ⟨k, hk⟩ := hm
    rw [hr1, h1, h2, fieldTy_knot (dmS fv) evK evD rfl ps (recOf_ev ps) 1 2 e he (by simp [evK, FTy.Lvl0, TyM.prop])]
    obtain ⟨e0, e1, rfl⟩ : ∃ e0 e1, e = [e0, e1] := by
      rcases e with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at he
      exact ⟨a, b, rfl⟩
    simp [evK, FTy.mean, Sem.asTy, es0, projIdx_ev2, Proto.parSem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show 0 < ps.length by omega)]
    simp at hk
    rw [← hk]
    rfl

/-- `Q`'s field type is the run's: `And` at `Q`'s own type, which means its truth, `False`. -/
theorem fields_q (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (ρ : Assignment)
    (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (hlen : ps.length = 0) (he : e.length = i)
    (hFT : fieldTerm qD c i = some FT)
    {r : Res} {s' : SState} (hr : run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D qD ps c e) = some (r, s')) :
    r.1.asTy = (dmS fv).fieldTy qD ps c i e := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hr
  subst hdm hΓ
  unfold run at hr
  have hps : ps = [] := List.eq_nil_of_length_eq_zero hlen
  subst hps
  have hc : c = 0 ∧ i = 0 ∧ FT = .tind "And" [.tind "Q" [], .tind "True" []] := by
    rcases c with _ | c <;> rcases i with _ | i <;> simp [fieldTerm, qD] at hFT <;> simp [hFT]
  obtain ⟨rfl, rfl, rfl⟩ := hc
  obtain ⟨d, v, w, T, U, s₁, s₂, hd, hv, hw, hr1⟩ := runT_tind2 _ ρ noFuture false _ "And" _ _ _ hr
  have hdd : d = andD := by dsimp only at hd; rw [find_and] at hd; exact (Option.some.inj hd).symm
  subst hdd
  obtain ⟨dq, hdq, hv1⟩ := runT_tind0 _ ρ noFuture false _ "Q" _ hv
  have hq : dq = qD := by dsimp only at hdq; rw [find_q] at hdq; exact (Option.some.inj hdq).symm
  subst hq
  obtain ⟨dt, hdt, hw1⟩ := runT_tind0 _ ρ noFuture false _ "True" _ hw
  have ht : dt = trueD := by dsimp only at hdt; rw [find_true] at hdt; exact (Option.some.inj hdt).symm
  subst ht
  simp only at hv1 hw1
  rw [hr1, hv1, hw1, fieldTy_knot (dmS fv) qK qD rfl [] (recOf_q []) 0 0 e he (by simp [qK, FTy.Lvl0])]
  dsimp only
  rw [tyM_and, tyM_q, tyM_true]
  simp [qK, FTy.mean, Sem.asTy]

/-- The library's two-parameter declarations at step 2's model: their fields are their parameters. -/
theorem fields_two (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (ρ : Assignment) (d : IndDecl)
    (hd2 : d = pairD ∨ d = andD) (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term) (hlen : ps.length = 2)
    (hpt : ParamsTyped (dmS fv) d ps) (he : e.length = i) (hFT : fieldTerm d c i = some FT)
    {r : Res} {s' : SState} (hr : run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D d ps c e) = some (r, s')) :
    r.1.asTy = (dmS fv).fieldTy d ps c i e := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hr
  subst hdm hΓ
  unfold run at hr
  obtain ⟨rfl, hi, rfl⟩ := fieldTerm_two hd2 hFT
  have harity : e.length ≤ DataLib.arity d 0 := by
    rcases hd2 with rfl | rfl <;> simp [DataLib.arity, pairD, andD] <;> omega
  have h1 := runT_teleFrame_param _ ρ noFuture false _ (dmS fv) D d ps 0 e harity i (by omega) (by omega) hr
  rw [h1]
  have hrec : (dmS fv).recOf d ps = recK (twoK d) ps := by rcases hd2 with rfl | rfl; exact recOf_pair ps; exact recOf_and ps
  -- the parameter is a type of level 1 or 0
  obtain ⟨A, cd, hA⟩ : ∃ (A : Type) (cd : Code0 A), ps[i] = .ty (.t0 A cd) := by
    rcases hd2 with rfl | rfl
    · obtain ⟨A, cd, hA, -⟩ := typed_univ1 hpt i (by omega) (paramTy_univ1 _ (by simp) i _)
      exact ⟨A, cd, hA⟩
    · obtain ⟨P, hP⟩ := typed_univ0 hpt i (by omega) (paramTy_and' i _)
      exact ⟨_, _, hP⟩
  have hp := parTy_of (show i < ps.length by omega) hA
  have hfty : ∀ es, (twoK d).fty (recK (twoK d)) ps 0 i es = .ty (parTy ps i) := by
    intro es
    show (if 0 = 0 ∧ i = 0 then FTy.ty (parTy ps 0) else if 0 = 0 ∧ i = 1 then FTy.ty (parTy ps 1) else FTy.ty TyM.err) = _
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp
  rw [fieldTy_knot (dmS fv) (twoK d) d rfl ps hrec 0 i e he (by rw [hfty, hp]; exact ⟨A, cd, rfl⟩), hfty, hp, hA]
  rfl

theorem find_bool : step2Decls.find? (·.name == "Bool") = some boolD := rfl

theorem tfD_idx : tfD.indexFields 0 = [0] := by decide

theorem uRead_eq : (dmS fv).read = uRead := rfl

/-- A member of `Bool` is one of its two constructors. -/
theorem bool_mem {v : Sem} (h : v ∈ₛ[uRead] uTyR boolD emptyRec) : ∃ k < 2, v = boolV k := by
  have h' : v ∈ₛ[dmPre.read] dmPre.tyR boolD emptyRec := h
  rw [DataModel.mem_tyR _ _ _ rfl] at h'
  obtain ⟨⟨c, hc⟩, fs, rfl, hf⟩ := (DataLib.mem_iff _ boolD emptyRec _).1 h'
  have hc2 : c < 2 := by simpa [boolD] using hc
  have ha : DataLib.arity boolD c = 0 := by
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> rfl
  rw [ha] at hf
  have : fs = [] := hf
  subst this
  exact ⟨c, hc2, rfl⟩

/-- **`TF`'s field types are the run's**: `Bool`, and the type the global `EvT` gives at the first
field, read through the call (whatever the call's state and the argument's type: `callOf_val`). -/
theorem fields_tf (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (hC : K.C.global "EvT" = fv)
    (hfv : EvTGood fv) (ρ : Assignment) (ps : List Sem) (c i : Nat) (e : List Sem) (FT : Term)
    (hlen : ps.length = 0) (hft : FieldsTyped (dmS fv) tfD ps c e) (he : e.length = i)
    (hFT : fieldTerm tfD c i = some FT)
    {r : Res} {s' : SState} (hr : run K ρ noFuture (.plain (TyM.univ 1)) FT (teleFrame K.dm K.D tfD ps c e) = some (r, s')) :
    r.1.asTy = (dmS fv).fieldTy tfD ps c i e := by
  cases K with
  | mk dm Γ C D Δ Λ cur =>
  dsimp only at hdm hΓ hC hr
  subst hdm hΓ hC
  unfold run at hr
  have hps : ps = [] := List.eq_nil_of_length_eq_zero hlen
  subst hps
  have hc : c = 0 ∧ (i = 0 ∧ FT = .tind "Bool" [] ∨ i = 1 ∧ FT = .call (.const "EvT") [.place (.var 1)] false) := by
    rcases c with _ | c <;> rcases i with _ | _ | i <;> simp [fieldTerm, tfD] at hFT <;> simp [hFT]
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hc
  · obtain ⟨d, hd, hr1⟩ := runT_tind0 _ ρ noFuture false _ "Bool" _ hr
    have hdd : d = boolD := by dsimp only at hd; rw [find_bool] at hd; exact (Option.some.inj hd).symm
    subst hdd
    rw [hr1, fieldTy_knot (dmS (C.global "EvT")) (tfK _) tfD rfl [] (recOf_tf []) 0 0 e he (by simp [tfK, FTy.Lvl0])]
    simp only [tfK, Sem.asTy, FTy.mean]
    unfold DataModel.tyM
    rw [recOf_bool]
    rfl
  · obtain ⟨as, s₁, r', s₂, has, hcall, hr1⟩ := runT_call_const _ ρ noFuture false _ "EvT" _ _ _ hr
    obtain ⟨v, T, s₃, hv, hasv⟩ := runArgs_one _ ρ noFuture _ _ _ _ has
    have har : e.length ≤ DataLib.arity tfD 0 := by simp [DataLib.arity, tfD]; omega
    have h1 := runT_teleFrame_field _ ρ noFuture false _ _ D tfD [] 0 e har 0 (by omega) (by simp [DataLib.arity, tfD]) hv
    simp only at h1
    subst h1
    obtain ⟨r'', s'', hcall', hr''⟩ := callOf_val _ _ as [(e[0], .plain TyM.err)] s₁ (emptyState 0) hcall (by rw [hasv]; rfl)
    -- `e[0]` is a `Bool`
    have hm := hft 0 (by omega)
    rw [fieldTy_knot (dmS (C.global "EvT")) (tfK _) tfD rfl [] (recOf_tf []) 0 0 _ (by simp) (by simp [tfK, FTy.Lvl0])] at hm
    simp only [tfK, FTy.mean] at hm
    obtain ⟨k, hk2, hk⟩ := bool_mem hm
    have hT : tfType (C.global "EvT") e[0] = r''.1.asTy := by
      unfold tfType
      rw [show uRead = (dmS (C.global "EvT")).read from rfl, hcall']
    obtain ⟨e0, rfl⟩ : ∃ e0, e = [e0] := by
      rcases e with _ | ⟨a, _ | _⟩ <;> simp at he
      exact ⟨a, rfl⟩
    simp only [List.getElem_cons_zero] at hk hT
    subst hk
    have hb : boolOf (projIdx tfD 0 [(boolV k).small]) = boolV k := by
      simp only [projIdx, tfD_idx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> rfl
    have hL : ((tfK (C.global "EvT")).fty (recK (tfK (C.global "EvT"))) [] 0 1 (projIdx tfD 0 ([boolV k].map Sem.small))).Lvl0 := by
      simp only [tfK, List.map_cons, List.map_nil, hb]
      rcases hfv k hk2 with ⟨A, cd, hA, -⟩ | hA
      · simp [hA, FTy.Lvl0]
      · simp [hA, FTy.Lvl0, TyM.err]
    rw [hr1, ← hr'', ← hT, fieldTy_knot (dmS (C.global "EvT")) (tfK _) tfD rfl [] (recOf_tf []) 0 1 _ he hL]
    simp only [tfK, List.map_cons, List.map_nil, hb]
    simp [FTy.mean]

/-- **`FieldsFaithful` at step 2's program.** -/
theorem fieldsFaithful (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls)
    (hC : K.C.global "EvT" = fv) (hfv : EvTGood fv) (ρ : Assignment) : FieldsFaithful K ρ := by
  intro d hd ps c i e FT hlen hpt hft he hFT r s' hr
  rw [hdm] at hpt hft ⊢
  rw [hΓ] at hd
  rcases mem_step2 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fields_two K hdm hΓ ρ pairD (.inl rfl) ps c i e FT (by simpa [pairD] using hlen) hpt he hFT hr
  · simp [fieldTerm, falseD] at hFT
  · rcases c with _ | c <;> simp [fieldTerm, trueD] at hFT
  · exact fields_two K hdm hΓ ρ andD (.inr rfl) ps c i e FT (by simpa [andD] using hlen) hpt he hFT hr
  · rcases c with _ | _ | c <;> simp [fieldTerm, boolD] at hFT
  · exact fields_list K hdm hΓ ρ ps c i e FT (by simpa [listD] using hlen) hpt he hFT hr
  · exact fields_rose K hdm hΓ ρ ps c i e FT (by simpa [roseD] using hlen) hpt he hFT hr
  · exact fields_tf K hdm hΓ hC hfv ρ ps c i e FT (by simpa [tfD] using hlen) hft he hFT hr
  · exact fields_ev K hdm hΓ ρ ps c i e FT (by simpa [evD] using hlen) hft he hFT hr
  · exact fields_q K hdm hΓ ρ ps c i e FT (by simpa [qD] using hlen) he hFT hr

/-- **`ParamsFaithful` at step 2's program**: the parameters' declared types run to their meanings. -/
theorem paramsFaithful (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (ρ : Assignment) :
    ParamsFaithful K ρ := by
  intro d hd ps j hn PT _ _ hPT r s' hr
  rw [hΓ] at hd
  unfold run at hr
  rw [hdm]
  have hsort : ∀ l, PT = .sort l → r.1.asTy = TyM.univ l := by
    intro l hl; subst hl; rw [runT_sort] at hr; cases hr; rfl
  rcases mem_step2 hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hsort 1 (by rcases j with _ | _ | j <;> simp [pairD] at hPT <;> exact hPT.2.symm), paramTy_univ1 _ (by simp)]
  · simp [falseD] at hPT
  · simp [trueD] at hPT
  · rw [hsort 0 (by rcases j with _ | _ | j <;> simp [andD] at hPT <;> exact hPT.2.symm), paramTy_and']
  · simp [boolD] at hPT
  · rw [hsort 1 (by rcases j with _ | j <;> simp [listD] at hPT <;> exact hPT.2.symm), paramTy_univ1 _ (by simp)]
  · rw [hsort 1 (by rcases j with _ | j <;> simp [roseD] at hPT <;> exact hPT.2.symm), paramTy_univ1 _ (by simp)]
  · simp [tfD] at hPT
  · have hP : PT = .nat := by rcases j with _ | j <;> simp [evD] at hPT <;> exact hPT.2.symm
    subst hP
    rw [runT_nat] at hr; cases hr
    rw [paramTy_ev]; rfl
  · simp [qD] at hPT

/-- **`CtxFaithful` at step 2's program.** -/
theorem ctxFaithful (K : RunCtx) (hdm : K.dm = (dmS fv)) (hΓ : K.Γ = step2Decls) (hC : K.C.global "EvT" = fv)
    (hfv : EvTGood fv) : CtxFaithful K :=
  fun Δ ρ => ⟨fieldsFaithful { K with Δ := Δ } hdm hΓ hC hfv ρ, paramsFaithful { K with Δ := Δ } hdm hΓ ρ,
    recordsFaithful K hdm hΓ hfv⟩

/-- **`DataFaithful` at every program state declaring step 2's program**, under any decisions,
whose global `EvT` means `fv`, at a meaning of `EvT` that gives a type of `Type₀` at either `Bool`;
at step 2's own list (the whole program being step 2's; docs/31 D174). -/
theorem dataFaithful (D : MState → Decisions) (P : ProgState) (hP : P.inds = step2Decls)
    (hC : P.baseC.global "EvT" = fv) (hfv : EvTGood fv) : Assembly.DataFaithful (dmS fv) D step2Decls P :=
  fun st _ _ => (ctxFaithful (P.ctx (dmS fv) D step2Decls st) rfl rfl hC hfv).prefix
    (by rw [hP]; exact List.prefix_refl _)

/-- The program state after step 2's declarations, with no global meaning recorded. -/
def step2State : ProgState := { inds := step2Decls }

/-- A meaning of `EvT` that does not run satisfies the hypothesis (its call is undefined). -/
theorem evTGood_err : EvTGood (.err, .plain TyM.err) := by
  intro k _
  right
  unfold tfType
  rfl

/-- **The existence statement's conclusion at step 2's program state**, under the checker's
decisions, at the state whose `EvT` has no recorded meaning. At the state the checker reaches (its
`EvT` the program meaning's), `dataFaithful` gives the same from `EvTGood` of that meaning. -/
theorem instance_data (fuel : Nat) :
    ∃ dm : DataModel, step2State.Covered dm ∧ Assembly.DataFaithful dm (chainDecisions fuel) step2Decls step2State :=
  ⟨dmS (.err, .plain TyM.err), fun _ _ => trivial, dataFaithful _ _ rfl rfl evTGood_err⟩

/-! ## A meaning of `EvT` that runs: the field `x` of `TF` exercised -/

/-- `EvT`'s parameter and result, as a function type's code reads them. -/
def evtDs : List PiDom := [⟨false, fun _ => uTyR boolD emptyRec⟩]
def evtOut : PiCod := ⟨false, fun _ => TyM.univ 1⟩

open Classical in
/-- What `EvT`'s body gives: `List(Nat)` at `true`, `Nat` otherwise. -/
noncomputable def evtTy (b : Sem) : TyM := if b = boolV 1 then uTyR listD (recK listK [.ty TyM.nat]) else TyM.nat

noncomputable def evtG (args : List Sem) : Option BodyOut := some ⟨.ty (evtTy (args.getD 0 .err)), [], none⟩

/-- **A closure meaning `EvT`**: built by the model's own closure construction at `Type₁`. -/
noncomputable def evtFv : Res := (closureAt uRead 2 noFuture evtDs evtOut evtG, .plain (piTyAt uRead 2 evtDs evtOut))

theorem evtTy_mem (b : Sem) : Sem.ty (evtTy b) ∈ₛ[uRead] TyM.univ 1 := by
  unfold evtTy
  split
  · exact ⟨⟨_, .data listD (recK listK [.ty TyM.nat]) _, rfl⟩, rfl⟩
  · exact ⟨⟨_, .nat, rfl⟩, rfl⟩

/-- Applied at a `Bool`, the closure gives `evtTy` (the model's `closure_apply'`). -/
theorem evtFv_call (b : Sem) (hb : b ∈ₛ[uRead] uTyR boolD emptyRec) (T : TyS) (s : SState) :
    ∃ s', callOf uRead evtFv [(b, T)] s = some ((.ty (evtTy b), .plain (TyM.univ 1)), s') := by
  have h := closure_apply' uRead 2 noFuture evtDs evtOut evtG ⟨by omega, by omega⟩ rfl
    (fun _ _ => show 2 ≤ 2 from Nat.le_refl _)
    (fun args _ => ⟨_, rfl, ⟨evtTy_mem _, fun i d hd hr => by
      rcases i with _ | i <;> simp [evtDs] at hd; subst hd; simp at hr⟩, rfl⟩)
    [(b, T)] s ⟨.ty (evtTy b), [], none⟩
    ⟨rfl, fun i a d ha hd => by
      rcases i with _ | i
      · simp [evtDs] at ha hd; subst ha hd; exact hb
      · simp at ha⟩
    (fun i d hd => by rcases i with _ | i <;> simp [evtDs] at hd; subst hd; show 1 ≤ 2; omega)
    trivial rfl
  exact h

theorem boolV_mem (k : Nat) (hk : k < 2) : boolV k ∈ₛ[uRead] uTyR boolD emptyRec := by
  have : boolV k ∈ₛ[dmPre.read] dmPre.tyR boolD emptyRec := by
    rw [DataModel.mem_tyR _ _ _ rfl]
    refine (DataLib.mem_iff _ boolD emptyRec _).2 ⟨⟨k, by simpa [boolD] using hk⟩, [], rfl, ?_⟩
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> rfl
  exact this

theorem tfType_evt (k : Nat) (hk : k < 2) : tfType evtFv (boolV k) = evtTy (boolV k) := by
  obtain ⟨s', h⟩ := evtFv_call (boolV k) (boolV_mem k hk) (.plain TyM.err) (emptyState 0)
  unfold tfType
  rw [h]
  rfl

/-- **The closure satisfies the hypothesis, and its call runs**: at either `Bool`, a level-1 type. -/
theorem evTGood_evt : EvTGood evtFv := by
  intro k hk
  left
  rw [tfType_evt k hk]
  unfold evtTy
  split
  · exact ⟨_, _, rfl, by simp [Code0.level, listD]⟩
  · exact ⟨_, _, rfl, rfl⟩

/-- At `true`, `TF`'s second field is `List(Nat)`, at `List`'s canonical record. -/
theorem tfType_true : tfType evtFv (boolV 1) = uTyR listD (recK listK [.ty TyM.nat]) := by
  rw [tfType_evt 1 (by omega)]; simp [evtTy]

/-- The program state after step 2's declarations, `EvT` meaning the closure. -/
noncomputable def step2StateEvT : ProgState := { inds := step2Decls, means := [("EvT", evtFv.1, evtFv.2)] }

/-- **The existence statement's conclusion at step 2's program, `EvT` meaning a closure whose call
runs** (so `TF`'s second field is faithful at a defined run: `List(Nat)` at `true`, `Nat` at `false`). -/
theorem instance_data_evt (fuel : Nat) :
    ∃ dm : DataModel, step2StateEvT.Covered dm ∧ Assembly.DataFaithful dm (chainDecisions fuel) step2Decls step2StateEvT :=
  ⟨dmS evtFv, fun _ _ => trivial, dataFaithful _ _ rfl rfl evTGood_evt⟩

end Ochr.Meaning.DataModel.Exists.Step2
