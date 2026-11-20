import Ochr.Meaning.Rules.Typed

/-!
# The rules trial, part A under the typing predicate: conversion is sound on well-typed values

`Rules/Sound.lean` states A for an instance of conversion's untyped parts that keeps meanings
(`SynSound`), which the machine's does not. Here A is proved for the machine's instance
(`Syn.machine`: `==` ignoring binder names and recorded parameters, the unit laws everywhere) on
values that are hereditarily well typed (`HWT`, `Rules/Typed.lean`).

The claim carried by the induction (`Alike2`) has two parts: two convertible values well typed at
one type mean the same there; two convertible type values, each well typed at a universe (not
necessarily the same: the model has no cumulativity, each type lies in exactly one universe), mean
the same at hint `err`, which is where `Eq`, `&` and the readings of a type read them.
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- A relation, pointwise on two lists of the same length. -/
inductive Fa2 {α β : Type _} (P : α → β → Prop) : List α → List β → Prop
  | nil : Fa2 P [] []
  | cons {a b as bs} : P a b → Fa2 P as bs → Fa2 P (a :: as) (b :: bs)

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A member of a declaration at a record is a constructor value recording that record. -/
theorem mem_dat {d : IndDecl} {r : Rec} {v : Sem} (h : K.dm.Mem d r v) : ∃ c fs, v = .dat d.name r c fs := by
  obtain ⟨k, x, rfl⟩ := h
  cases k with
  | zero => exact x.elim
  | succ k => exact ⟨_, _, rfl⟩

/-- A (partly moved) member of a data type of the model that is a constructor value records the
type's record. -/
theorem pmem_dat_rec {d : IndDecl} {r r' : Rec} {n : String} {c : Nat} {ms : List Sem}
    (hs : (d.sort == 0) = false)
    (h : DataModel.pmem K.dm.read K.Γ (.dat n r' c ms) (K.dm.tyR d r)) : r' = r := by
  rcases h with h | ⟨t, -, hmo, hin⟩
  · cases h
  · have key : ∀ t', (t' ∈ₛ[K.dm.read] K.dm.tyR d r ∨ DataModel.OpenIn K.dm.read (K.dm.tyR d r) t') →
        ∀ n' c' gs, t' = .dat n' r' c' gs → r' = r := by
      intro t' hin' n' c' gs e
      subst e
      rcases hin' with hm | ho
      · obtain ⟨c'', fs'', e⟩ := mem_dat K ((K.dm.mem_tyR d r hs _).1 hm)
        cases e; rfl
      · unfold DataModel.tyR at ho
        rw [hs] at ho
        exact ho.2.1.symm
    cases hmo with
    | refl => exact key _ hin _ _ _ rfl
    | dat _ => exact key _ hin _ _ _ rfl
    | succ _ =>
      exfalso
      rcases hin with hm | ho
      · obtain ⟨c'', fs'', e⟩ := mem_dat K ((K.dm.mem_tyR d r hs _).1 hm)
        cases e
      · unfold DataModel.tyR at ho
        rw [hs] at ho
        exact ho

/-- `err` is no partly moved member of anything. -/
theorem not_pmem_err (T : TyM) : ¬ DataModel.pmem K.dm.read K.Γ .err T := by
  rintro (h | ⟨t, hw, hmo, -⟩)
  · cases h
  · cases hmo with
    | refl => simp [Sem.whole] at hw

/-- **The pinning lemma** (handoff step 4): a well-typed constructor value at a data type of the
model means the constructor value at the type's record, whatever parameters it records. -/
theorem meanV_ind_pinned {T : TyM} {t : String} {c : Nat} {h : Hint} {ps fs : List Value} {d : IndDecl}
    {r : Rec} (hm : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.ind t c h ps fs)) T)
    (hd : K.Γ.find? (·.name == t) = some d) (hs : (d.sort == 0) = false) (hT : T = K.dm.tyR d r) :
    meanV K ρ φ (.plain T) (.ind t c h ps fs) = .dat t r c (meanFields K ρ φ d r c 0 [] fs) := by
  have hname : d.name = t := by
    have := List.find?_some hd
    simpa using this
  revert hm
  simp only [meanV, hd]
  split
  · rename_i r' _
    simp only [hs, Bool.false_eq_true, reduceIte, DataModel.ctorR]
    intro hm
    subst hT
    have e := pmem_dat_rec K hs hm
    subst e
    rw [hname]
  · intro hm; exact absurd hm (not_pmem_err K _)

/-- **The claim**: two values alike under the typing predicate. -/
def Alike2 (v w : Value) : Prop :=
  (∀ T, HWT K ρ φ T v → HWT K ρ φ T w → meanV K ρ φ (.plain T) v = meanV K ρ φ (.plain T) w) ∧
  (∀ l l', HWT K ρ φ (TyM.univ l) v → HWT K ρ φ (TyM.univ l') w →
    meanV K ρ φ (.plain .err) v = meanV K ρ φ (.plain .err) w)

theorem Alike2.rfl' (v : Value) : Alike2 K ρ φ v v := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Alike parameters mean alike, each at its parameter type. -/
theorem meanParams_alike (d : IndDecl) : ∀ {as bs : List Value} {i : Nat} {e : List Sem},
    Fa2 (Alike2 K ρ φ) as bs → HWTParams K ρ φ d i e as → HWTParams K ρ φ d i e bs →
    meanParams K ρ φ d i e as = meanParams K ρ φ d i e bs
  | [], [], _, _, .nil, _, _ => rfl
  | a :: as, b :: bs, i, e, .cons hab hrest, ha, hb => by
    cases ha with
    | cons ha1 ha2 =>
      cases hb with
      | cons hb1 hb2 =>
        have e1 := hab.1 _ ha1 hb1
        simp only [meanParams]
        rw [e1] at ha2 ⊢
        rw [meanParams_alike d hrest ha2 hb2]

/-- Alike fields mean alike, each at its field type. -/
theorem meanFields_alike (d : IndDecl) (r : Rec) (c : Nat) : ∀ {as bs : List Value} {i : Nat} {e : List Sem},
    Fa2 (Alike2 K ρ φ) as bs → HWTFields K ρ φ d r c i e as → HWTFields K ρ φ d r c i e bs →
    meanFields K ρ φ d r c i e as = meanFields K ρ φ d r c i e bs
  | [], [], _, _, .nil, _, _ => rfl
  | a :: as, b :: bs, i, e, .cons hab hrest, ha, hb => by
    cases ha with
    | cons ha1 ha2 =>
      cases hb with
      | cons hb1 hb2 =>
        have e1 := hab.1 _ ha1 hb1
        simp only [meanFields]
        rw [e1] at ha2 ⊢
        rw [meanFields_alike d r c hrest ha2 hb2]

/-- A universe is no data type of the model. -/
theorem univ_ne_tyR (l : Nat) (d : IndDecl) (r : Rec) (hs : (d.sort == 0) = false) :
    TyM.univ l ≠ K.dm.tyR d r := by
  intro e
  have := congrArg TyM.dataRec? e
  unfold DataModel.tyR at this
  rw [hs] at this
  match l with
  | 0 | 1 | 2 | _ + 3 => simp [TyM.univ, TyM.dataRec?, TyM.err] at this

theorem tyR_rec_inj {d : IndDecl} {r r' : Rec} (hs : (d.sort == 0) = false) (e : K.dm.tyR d r = K.dm.tyR d r') :
    r = r' := by
  have := congrArg TyM.dataRec? e
  unfold DataModel.tyR at this
  rw [hs] at this
  simpa [TyM.dataRec?] using this

end

/-- Code values: a closure, a Π-closure, a sealed program (their meaning is a run of their code). -/
def isCode : Value → Bool
  | .clo .. | .tPi .. | .sealed _ => true
  | _ => false

/-- A predicate on values closed under the first-order components conversion compares, and
under the unit laws. Instances: no code at all (`FO`); the [Close]-shape invariant. -/
structure Closed (Q : Value → Prop) : Prop where
  succ : ∀ {a}, Q (.succ a) → Q a
  tRef : ∀ {a}, Q (.tRef a) → Q a
  borrow : ∀ {l a}, Q (.borrow l a) → Q a
  gloan : ∀ {l a}, Q (.gloan l a) → Q a
  tEq : ∀ {A a b}, Q (.tEq A a b) → Q A ∧ Q a ∧ Q b
  tInd : ∀ {n as}, Q (.tInd n as) → ∀ a ∈ as, Q a
  ind : ∀ {t c h ps fs}, Q (.ind t c h ps fs) → ∀ a ∈ fs, Q a
  unit : ∀ {v}, Q v → Q (unitTop v)

theorem fa2_of_beqList {P : Value → Value → Prop} : ∀ (as bs : List Value), Value.beqList as bs = true →
    (∀ a ∈ as, ∀ b ∈ bs, Value.beq a b = true → P a b) → Fa2 P as bs
  | [], [], _, _ => .nil
  | a :: as, b :: bs, h, hp => by
    simp only [Value.beqList, Bool.and_eq_true] at h
    exact .cons (hp a (List.mem_cons_self ..) b (List.mem_cons_self ..) h.1)
      (fa2_of_beqList as bs h.2 fun x hx y hy hxy => hp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
  | [], _ :: _, h, _ => by simp [Value.beqList] at h
  | _ :: _, [], h, _ => by simp [Value.beqList] at h

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-! ### The congruence of each first-order former, for the claim -/

theorem alike_succ {a b : Value} (ih : Alike2 K ρ φ a b) : Alike2 K ρ φ (.succ a) (.succ b) := by
  have key : ∀ T T', HWT K ρ φ T (.succ a) → HWT K ρ φ T' (.succ b) →
      ∀ hint hint', meanV K ρ φ hint (.succ a) = meanV K ρ φ hint' (.succ b) := by
    intro T T' ha hb hint hint'
    cases ha with
    | atom hx _ => exact hx.elim
    | succ _ ha =>
      cases hb with
      | atom hx _ => exact hx.elim
      | succ _ hb => simp only [meanV]; rw [ih.1 _ ha hb]
  exact ⟨fun T ha hb => key _ _ ha hb _ _, fun l l' ha hb => key _ _ ha hb _ _⟩

theorem alike_tRef {A B : Value} (ih : Alike2 K ρ φ A B) : Alike2 K ρ φ (.tRef A) (.tRef B) := by
  have key : ∀ T T', HWT K ρ φ T (.tRef A) → HWT K ρ φ T' (.tRef B) →
      ∀ hint hint', meanV K ρ φ hint (.tRef A) = meanV K ρ φ hint' (.tRef B) := by
    intro T T' ha hb hint hint'
    cases ha with
    | atom hx _ => exact hx.elim
    | tRef _ ha =>
      cases hb with
      | atom hx _ => exact hx.elim
      | tRef _ hb => simp only [meanV]; exact ih.2 _ _ ha hb
  exact ⟨fun T ha hb => key _ _ ha hb _ _, fun l l' ha hb => key _ _ ha hb _ _⟩

theorem alike_borrow {l : Nat} {a b : Value} (ih : Alike2 K ρ φ a b) :
    Alike2 K ρ φ (.borrow l a) (.borrow l b) := by
  refine ⟨fun T ha hb => ?_, fun l₁ l₂ ha hb => ?_⟩
  · cases ha with
    | atom hx _ => exact hx.elim
    | borrow ha => cases hb with
      | atom hx _ => exact hx.elim
      | borrow hb => simp only [meanV]; exact ih.1 _ ha hb
  · cases ha with
    | atom hx _ => exact hx.elim
    | borrow ha => cases hb with
      | atom hx _ => exact hx.elim
      | borrow hb => simp only [meanV]; exact ih.2 _ _ ha hb

theorem alike_gloan {l : Nat} {a b : Value} (ih : Alike2 K ρ φ a b) :
    Alike2 K ρ φ (.gloan l a) (.gloan l b) := by
  refine ⟨fun T ha hb => ?_, fun l₁ l₂ ha hb => ?_⟩
  · cases ha with
    | atom hx _ => exact hx.elim
    | gloan ha => cases hb with
      | atom hx _ => exact hx.elim
      | gloan hb => simp only [meanV]; exact ih.1 _ ha hb
  · cases ha with
    | atom hx _ => exact hx.elim
    | gloan ha => cases hb with
      | atom hx _ => exact hx.elim
      | gloan hb => simp only [meanV]; exact ih.2 _ _ ha hb

theorem alike_tEq {A a b B c d : Value} (ihA : Alike2 K ρ φ A B) (iha : Alike2 K ρ φ a c)
    (ihb : Alike2 K ρ φ b d) : Alike2 K ρ φ (.tEq A a b) (.tEq B c d) := by
  have key : ∀ T T', HWT K ρ φ T (.tEq A a b) → HWT K ρ φ T' (.tEq B c d) →
      ∀ hint hint', meanV K ρ φ hint (.tEq A a b) = meanV K ρ φ hint' (.tEq B c d) := by
    intro T T' h1 h2 hint hint'
    cases h1 with
    | atom hx _ => exact hx.elim
    | tEq _ hA ha hb =>
      cases h2 with
      | atom hx _ => exact hx.elim
      | tEq _ hB hc' hd' =>
        have eA := ihA.2 _ _ hA hB
        have ety : tyOf K ρ φ B = tyOf K ρ φ A := by simp only [tyOf]; rw [eA]
        rw [ety] at hc' hd'
        simp only [meanV]
        rw [← eA, iha.1 _ ha hc', ihb.1 _ hb hd']
  exact ⟨fun T ha hb => key _ _ ha hb _ _, fun l l' ha hb => key _ _ ha hb _ _⟩

theorem alike_tInd {n : String} {as bs : List Value} (fa : Fa2 (Alike2 K ρ φ) as bs) :
    Alike2 K ρ φ (.tInd n as) (.tInd n bs) := by
  have key : ∀ T T', HWT K ρ φ T (.tInd n as) → HWT K ρ φ T' (.tInd n bs) →
      ∀ hint hint', meanV K ρ φ hint (.tInd n as) = meanV K ρ φ hint' (.tInd n bs) := by
    intro T T' h1 h2 hint hint'
    cases h1 with
    | atom hx _ => exact hx.elim
    | tInd _ hd hps =>
      cases h2 with
      | atom hx _ => exact hx.elim
      | tInd _ hd' hqs =>
        rw [hd] at hd'
        cases hd'
        simp only [meanV, hd]
        rw [meanParams_alike K ρ φ _ fa hps hqs]
  exact ⟨fun T ha hb => key _ _ ha hb _ _, fun l l' ha hb => key _ _ ha hb _ _⟩

/-- A constructor value by its constructor and fields, whatever parameters the two record (the
pinning lemma does the work). -/
theorem alike_ind {t : String} {c : Nat} {hh hh' : Hint} {ps qs fs gs : List Value}
    (fa : Fa2 (Alike2 K ρ φ) fs gs) : Alike2 K ρ φ (.ind t c hh ps fs) (.ind t c hh' qs gs) := by
  refine ⟨fun T h1 h2 => ?_, fun l l' h1 h2 => ?_⟩
  · cases h1 with
    | atom hx _ => exact hx.elim
    | ind hm hd hs hT _ hfs =>
      cases h2 with
      | atom hx _ => exact hx.elim
      | ind hm' hd' hs' hT' _ hgs =>
        rw [hd] at hd'
        cases hd'
        have er := tyR_rec_inj K hs (hT.symm.trans hT')
        subst er
        rw [meanV_ind_pinned K ρ φ hm hd hs hT, meanV_ind_pinned K ρ φ hm' hd hs hT',
          meanFields_alike K ρ φ _ _ _ fa hfs hgs]
  · cases h1 with
    | atom hx _ => exact hx.elim
    | ind _ _ hs hT _ _ => exact absurd hT (univ_ne_tyR K _ _ _ hs)

/-- **`==` is sound on well-typed values** (handoff step 5; [Conv-refl] for the machine's
instance), for values in a closed class `Q`, given the code case (`hc`). -/
theorem beq_alike {Q : Value → Prop} (hQ : Closed Q)
    (hc : ∀ v w, Q v → Q w → isCode v = true → Value.beq v w = true → Alike2 K ρ φ v w)
    (v w : Value) (hv : Q v) (hw : Q w) (h : Value.beq v w = true) : Alike2 K ρ φ v w :=
  match v with
  | .zero | .unit | .bot | .proof | .tNat | .tUnit => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h <;> exact Alike2.rfl' K ρ φ _
  | .gfn n => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, beq_iff_eq] at h
    subst h; exact Alike2.rfl' K ρ φ _
  | .loan l | .abs l | .sort l => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, beq_iff_eq] at h
    all_goals (subst h; exact Alike2.rfl' K ρ φ _)
  | .clo .. | .tPi .. | .sealed _ => hc _ w hv hw rfl h
  | .succ a => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h
    exact alike_succ K ρ φ (beq_alike hQ hc a _ (hQ.succ hv) (hQ.succ hw) h)
  | .tRef A => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h
    exact alike_tRef K ρ φ (beq_alike hQ hc A _ (hQ.tRef hv) (hQ.tRef hw) h)
  | .borrow l a => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact alike_borrow K ρ φ (beq_alike hQ hc a _ (hQ.borrow hv) (hQ.borrow hw) h)
  | .gloan l a => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact alike_gloan K ρ φ (beq_alike hQ hc a _ (hQ.gloan hv) (hQ.gloan hw) h)
  | .tEq A a b => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hAB, hac⟩, hbd⟩ := h
    obtain ⟨qA, qa, qb⟩ := hQ.tEq hv
    obtain ⟨qB, qc, qd⟩ := hQ.tEq hw
    exact alike_tEq K ρ φ (beq_alike hQ hc A _ qA qB hAB) (beq_alike hQ hc a _ qa qc hac)
      (beq_alike hQ hc b _ qb qd hbd)
  | .tInd n as => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rename_i m bs
    obtain ⟨rfl, h⟩ := h
    exact alike_tInd K ρ φ (fa2_of_beqList as bs h fun x hx y hy hxy =>
      beq_alike hQ hc x y (hQ.tInd hv x hx) (hQ.tInd hw y hy) hxy)
  | .ind t c hh ps fs => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rename_i u c' hh' qs gs
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    exact alike_ind K ρ φ (fa2_of_beqList fs gs h fun x hx y hy hxy =>
      beq_alike hQ hc x y (hQ.ind hv x hx) (hQ.ind hw y hy) hxy)
termination_by sizeOf v

/-! ### What A takes as given, each named -/

/-- [Conv-fun]'s and [Conv-pi]'s premises are sound, in the claim's form: the abstract premise
(in the machine's instance: a successful generic call, a successful comparison of the generic
arguments' types) makes the two values alike. The whole semantic content of the function rules. -/
structure PremSoundT (G : Premises) : Prop where
  fn : ∀ f g, G.fn f g → Alike2 K ρ φ f g
  pi : ∀ P Q, G.pi P Q → Alike2 K ρ φ P Q

/-- The unit laws keep a well-typed value well typed and keep its meaning (a fact about the
library's `True` and `And` in the data model: `And(True, P)` means `True ∧ ⟦P⟧`). -/
structure UnitOk (Q : Value → Prop) : Prop where
  hwt : ∀ T v, Q v → HWT K ρ φ T v → HWT K ρ φ T (unitTop v)
  mean : ∀ T v, Q v → HWT K ρ φ T v → meanV K ρ φ (.plain T) (unitTop v) = meanV K ρ φ (.plain T) v
  meanErr : ∀ l v, Q v → HWT K ρ φ (TyM.univ l) v →
    meanV K ρ φ (.plain .err) (unitTop v) = meanV K ρ φ (.plain .err) v

/-- The code cases: [Conv-refl] on code (`==` up to binder names and recorded parameters),
[Conv-cong] on sealed programs and on Π-closures' code. Not true of every well-typed value
(`Rules/CodeCE.lean`); stated for the values of a class `Q` (the [Close]-shape invariant), where it
is the handoff's step 7. -/
structure CodeOk (Q : Value → Prop) (G : Premises) (gs : List GDef) : Prop where
  refl : ∀ v w, Q v → Q w → isCode v = true → Value.beq v w = true → Alike2 K ρ φ v w
  sealed : ∀ t u, Q (.sealed t) → Q (.sealed u) → ConvT Syn.machine G gs t u → Alike2 K ρ φ (.sealed t) (.sealed u)
  piCong : ∀ cs ds t u r r', Q (.tPi cs t r) → Q (.tPi ds u r') → RdEq Syn.machine r r' →
    ConvL Syn.machine G gs cs ds → ConvT Syn.machine G gs t u → Alike2 K ρ φ (.tPi cs t r) (.tPi ds u r')

variable {K ρ φ} {Q : Value → Prop} {G : Premises} {gs : List GDef}

/-- The unit laws applied to both sides keep the claim. -/
theorem alike_of_unitTop (hu : UnitOk K ρ φ Q) {v w : Value} (hv : Q v) (hw : Q w)
    (ih : Alike2 K ρ φ (unitTop v) (unitTop w)) : Alike2 K ρ φ v w := by
  refine ⟨fun T ha hb => ?_, fun l l' ha hb => ?_⟩
  · rw [← hu.mean T v hv ha, ← hu.mean T w hw hb]
    exact ih.1 T (hu.hwt T v hv ha) (hu.hwt T w hw hb)
  · rw [← hu.meanErr l v hv ha, ← hu.meanErr l' w hw hb]
    exact ih.2 l l' (hu.hwt _ v hv ha) (hu.hwt _ w hw hb)

mutual
/-- **(A) Conversion is sound on well-typed values** (handoff step 6), by induction on the
derivation in the machine's instance. -/
theorem convV_alike (hQ : Closed Q) (hp : PremSoundT K ρ φ G) (hu : UnitOk K ρ φ Q) (hc : CodeOk K ρ φ Q G gs) :
    ∀ {v w : Value}, ConvV Syn.machine G gs v w → Q v → Q w → Alike2 K ρ φ v w
  | _, _, .refl h, hv, hw => beq_alike K ρ φ hQ hc.refl _ _ hv hw h
  | _, _, .unit _ _ d, hv, hw =>
    alike_of_unitTop hu hv hw (convH_alike hQ hp hu hc d (hQ.unit hv) (hQ.unit hw))

theorem convH_alike (hQ : Closed Q) (hp : PremSoundT K ρ φ G) (hu : UnitOk K ρ φ Q) (hc : CodeOk K ρ φ Q G gs) :
    ∀ {v w : Value}, ConvH Syn.machine G gs v w → Q v → Q w → Alike2 K ρ φ v w
  | _, _, .refl h, hv, hw => beq_alike K ρ φ hQ hc.refl _ _ hv hw h
  | _, _, .succ d, hv, hw => alike_succ K ρ φ (convV_alike hQ hp hu hc d (hQ.succ hv) (hQ.succ hw))
  | _, _, .tRef d, hv, hw => alike_tRef K ρ φ (convV_alike hQ hp hu hc d (hQ.tRef hv) (hQ.tRef hw))
  | _, _, .tInd d, hv, hw => alike_tInd K ρ φ (convL_alike hQ hp hu hc d (hQ.tInd hv) (hQ.tInd hw))
  | _, _, .tEq d1 d2 d3, hv, hw =>
    alike_tEq K ρ φ (convV_alike hQ hp hu hc d1 (hQ.tEq hv).1 (hQ.tEq hw).1)
      (convV_alike hQ hp hu hc d2 (hQ.tEq hv).2.1 (hQ.tEq hw).2.1)
      (convV_alike hQ hp hu hc d3 (hQ.tEq hv).2.2 (hQ.tEq hw).2.2)
  | _, _, .borrow d, hv, hw => alike_borrow K ρ φ (convV_alike hQ hp hu hc d (hQ.borrow hv) (hQ.borrow hw))
  | _, _, .ind _ d, hv, hw => alike_ind K ρ φ (convL_alike hQ hp hu hc d (hQ.ind hv) (hQ.ind hw))
  | _, _, .sealed d, hv, hw => hc.sealed _ _ hv hw d
  | _, _, .piCong hr dl dt, hv, hw => hc.piCong _ _ _ _ _ _ hv hw hr dl dt
  | _, _, .pi h, _, _ => hp.pi _ _ h
  | _, _, .fn _ _ _ _ _ _ h, _, _ => hp.fn _ _ h

theorem convL_alike (hQ : Closed Q) (hp : PremSoundT K ρ φ G) (hu : UnitOk K ρ φ Q) (hc : CodeOk K ρ φ Q G gs) :
    ∀ {as bs : List Value}, ConvL Syn.machine G gs as bs → (∀ a ∈ as, Q a) → (∀ b ∈ bs, Q b) →
      Fa2 (Alike2 K ρ φ) as bs
  | _, _, .nil, _, _ => .nil
  | _, _, .cons d ds, ha, hb =>
    .cons (convV_alike hQ hp hu hc d (ha _ (List.mem_cons_self ..)) (hb _ (List.mem_cons_self ..)))
      (convL_alike hQ hp hu hc ds (fun a h => ha a (List.mem_cons_of_mem _ h)) (fun b h => hb b (List.mem_cons_of_mem _ h)))
end

end

/-! ### The first-order fragment: no code, so `CodeOk` holds outright -/

/-- A value with no code in the parts conversion compares (no closure, Π-closure or sealed program
outside a constructor value's recorded parameters, which neither `==` nor conversion reads). -/
inductive FO : Value → Prop
  | atom {v : Value} : isCode v = false → (match v with
      | .succ _ | .tRef _ | .borrow .. | .gloan .. | .tEq .. | .tInd .. | .ind .. => False | _ => True) → FO v
  | succ {a : Value} : FO a → FO (.succ a)
  | tRef {a : Value} : FO a → FO (.tRef a)
  | borrow {l : Nat} {a : Value} : FO a → FO (.borrow l a)
  | gloan {l : Nat} {a : Value} : FO a → FO (.gloan l a)
  | tEq {A a b : Value} : FO A → FO a → FO b → FO (.tEq A a b)
  | tInd {n : String} {as : List Value} : (∀ a ∈ as, FO a) → FO (.tInd n as)
  | ind {t : String} {c : Nat} {h : Hint} {ps fs : List Value} : (∀ a ∈ fs, FO a) → FO (.ind t c h ps fs)

theorem FO.not_code {v : Value} (h : FO v) : isCode v = false := by
  cases h with
  | atom hc _ => exact hc
  | _ => rfl

theorem FO.mkAnd {p q : Value} (hp : FO p) (hq : FO q) : FO (Ochr.mkAnd p q) := by
  unfold Ochr.mkAnd
  split
  · exact hq
  · exact hp
  · exact .tInd fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hp
      · exact hq

theorem FO.unitTop : ∀ (v : Value), FO v → FO (unitTop v) := by
  intro v
  induction v using unitTop.induct with
  | case1 p q ihp ihq =>
    intro h
    rw [Ochr.unitTop]
    cases h with
    | atom _ hx => exact hx.elim
    | tInd hs => exact FO.mkAnd (ihp (hs p (by simp))) (ihq (hs q (by simp)))
  | case2 v hv => intro h; rw [Ochr.unitTop.eq_2 v hv]; exact h

theorem FO.closed : Closed FO where
  succ h := by cases h with | atom _ hx => exact hx.elim | succ h => exact h
  tRef h := by cases h with | atom _ hx => exact hx.elim | tRef h => exact h
  borrow h := by cases h with | atom _ hx => exact hx.elim | borrow h => exact h
  gloan h := by cases h with | atom _ hx => exact hx.elim | gloan h => exact h
  tEq h := by cases h with | atom _ hx => exact hx.elim | tEq h1 h2 h3 => exact ⟨h1, h2, h3⟩
  tInd h := by cases h with | atom _ hx => exact hx.elim | tInd h => exact h
  ind h := by cases h with | atom _ hx => exact hx.elim | ind h => exact h
  unit h := FO.unitTop _ h

theorem FO.codeOk (K : RunCtx) (ρ : Assignment) (φ : Future) (G : Premises) (gs : List GDef) :
    CodeOk K ρ φ FO G gs where
  refl v _ hv _ hc _ := by rw [hv.not_code] at hc; cases hc
  sealed _ _ hv _ _ := by have := hv.not_code; simp [isCode] at this
  piCong _ _ _ _ _ _ hv _ _ _ _ := by have := hv.not_code; simp [isCode] at this

/-- **(A) for the first-order fragment**: convertible values with no code, both well typed,
are alike, resting only on the function rules' premises and the unit laws. -/
theorem convV_alike_fo {K : RunCtx} {ρ : Assignment} {φ : Future} {G : Premises} {gs : List GDef}
    (hp : PremSoundT K ρ φ G) (hu : UnitOk K ρ φ FO) {v w : Value} (h : ConvV Syn.machine G gs v w)
    (hv : FO v) (hw : FO w) : Alike2 K ρ φ v w :=
  convV_alike FO.closed hp hu (FO.codeOk K ρ φ G gs) h hv hw

end Ochr.Meaning.Rules

#print axioms Ochr.Meaning.Rules.convV_alike
#print axioms Ochr.Meaning.Rules.convV_alike_fo
