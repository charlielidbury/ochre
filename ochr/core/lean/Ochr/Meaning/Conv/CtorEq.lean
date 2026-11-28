import Ochr.Meaning.Conv.Ctor
import Ochr.Meaning.Conv.SoundEq
import Ochr.Meaning.Conv.FieldIdx

/-!
# `Eq` at constructor values (conv2, 2026-11-28)

Part A for `Eq` on sides that hold no code (`FO`), constructor values included: [Eq-disj] at two
constructors (the refutation), [Eq-inj] (injectivity, D64's restriction included), and the rules
already proved on plain sides. The named premises (each classed; status in the report):

* `FieldTysOk` (X; conv1's `FieldTysSound`, RESTATED): the field types [Eq-inj] computes mean the
  model's field types, and have a level, at parameters typed and of the declaration's length and
  earlier fields typed. As conv1 stated it (at every parameter list) it is not derivable: faithfulness
  speaks of typed parameters only (`FieldsFaithful`, `RecordsFaithful`), and at untyped parameters
  the record is arbitrary. Its content is (II) for `fieldTele`'s typed runs and `FieldsFaithful`.
* (main's D144, from branch `conv2-eqargs`) [Eq-inj] is at the equation's type `D(ā)` by the rule itself (`eqArgs_ind`): the
  checker no longer falls back to the values' own recorded parameters, so conv1's premises (a) and (b) are
  met by construction (the program's `D` at typed parameters) and no class condition is asked of the sides.
* `LeafsOk` (M): a record at typed parameters of a declaration has no junk leaf at its genuine keys
  (`RecordsFaithful.leafOk`, which `CtxS.faithful` carries for the checker's declarations).
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.DataModel Ochr.Meaning.DataLib

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **(H6') [Eq-inj]'s field types, restated** (X): computed at parameters that are typed, with the
earlier fields typed, each field type means the model's field type at the parameters' record and the
earlier fields, and has a level. Its content: (II) for `fieldTele`'s typed runs and `FieldsFaithful`. -/
def FieldTysSoundT (G : Premises) : Prop :=
  ∀ d args c fs Ts, G.fieldTys d args c fs Ts →
    paramsOk K.dm d (meanParams K ρ φ d 0 [] args) →
    ∀ j T, Ts[j]? = some T →
      (∀ i f, i < j → (meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs)[i]? = some f →
        f ∈ₛ[K.dm.read] K.dm.fieldTyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c i
          ((meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs).take i)) →
      capTy K ρ φ T = K.dm.fieldTyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c j
          ((meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs).take j) ∧
        (capTy K ρ φ T).level.isSome = true

/-- `FieldTysSoundT`, and the parameters [Eq-inj] uses are of the declaration's length (C; `fieldTele` fails
otherwise: `FieldLen.machPremises_len`, PROVED for the machine's instance). -/
structure FieldTysOk (G : Premises) : Prop where
  len : ∀ d args c fs Ts, G.fieldTys d args c fs Ts → args.length = d.params.length
  sound : FieldTysSoundT K ρ φ G

end

/-- (M) Records at typed parameters of the declarations `Γ` finds have no junk leaf at their genuine
keys (`RecordsFaithful.leafOk`). -/
def LeafsOk (K : RunCtx) (Γ : List IndDecl) : Prop :=
  ∀ t d, Γ.find? (·.name == t) = some d → ∀ ps, ps.length = d.params.length → ParamsTyped K.dm d ps →
    K.dm.RecLeafOk d (K.dm.recOf d ps)

theorem paramsTyped_of_ok {dm : DataModel} {d : IndDecl} {ps : List Sem} (h : paramsOk dm d ps) :
    ParamsTyped dm d ps := fun j hj => h j _ (List.getElem?_eq_getElem hj)

/-! ## Helpers about the universal signature's shapes -/

theorem TyM.isErr_err : TyM.err.isErr = true := rfl

/-- A shape the universal signature gives at a genuine key, fitted by some meaning, is not typed
`err`. -/
theorem shapeTy_ne_err (dm : DataModel) {d : IndDecl} {r : Rec} {c i : Nat} {es : List Small} {f : Sem}
    (h : FitsOneM dm.sig (dm.sig.shape d r c i es) f) : dm.shapeTy (dm.sig.shape d r c i es) ≠ TyM.err := by
  intro he
  change FitsOneM uSig (uShape d r c i es) f at h
  change dm.shapeTy (uShape d r c i es) = TyM.err at he
  unfold uShape at h he
  generalize r (kindKey c i (projIdx d c es)) = en at h he
  cases en with
  | data d' =>
    dsimp only at h he
    by_cases hs : (d'.sort == 0) = true
    · rw [if_pos hs] at h he
      have := congrArg TyM.isErr he
      simp [DataModel.shapeTy, hs, DataModel.tyR, TyM.prop, TyM.isErr, TyM.err] at this
    · rw [if_neg hs] at h he
      have := congrArg TyM.isErr he
      simp [DataModel.shapeTy, hs, DataModel.tyR, TyM.isErr, TyM.err] at this
  | leaf B cd =>
    dsimp only at h he
    cases cd with
    | err => obtain ⟨b, -⟩ := h; exact b.elim
    | _ =>
      have := congrArg TyM.isErr he
      simp [DataModel.shapeTy, TyM.isErr, TyM.err] at this
  | none => obtain ⟨b, -⟩ := h; exact b.elim
  | small _ => obtain ⟨b, -⟩ := h; exact b.elim

/-- **A fitting field at a genuine key of a record without junk leaves is a member of its field type.** -/
theorem fits_mem_fieldTy (dm : DataModel) {d : IndDecl} {r : Rec} {c i : Nat} {e : List Sem} {f : Sem}
    (hok : dm.RecLeafOk d r) (hc : c < d.ctors.length) (hi : i < arity d c) (hl : e.length = i)
    (h : FitsOneM dm.sig (dm.sig.shape d r c i (e.map Sem.small)) f) : f ∈ₛ[dm.read] dm.fieldTyR d r c i e :=
  dm.fitsOneM_mem _ f h (shapeTy_ne_err dm h) (hok c i _ hc hi (by simpa using hl))

theorem fitsM_length (S : Sig) (d : IndDecl) (r : Rec) (c : Nat) :
    ∀ (n i : Nat) (e : List Small) (fs : List Sem), FitsM S d r c i n e fs → fs.length = n
  | 0, _, _, fs, h => by have : fs = [] := h; subst this; rfl
  | n + 1, i, e, fs, ⟨f, fs', hfs, _, h2⟩ => by
    subst hfs; simp [fitsM_length S d r c n (i + 1) _ fs' h2]

/-- The fields of a member fitting its telescope, at a record without junk leaves, are members of
their field types. -/
theorem fitsM_typed (dm : DataModel) {d : IndDecl} {r : Rec} {c : Nat} {F : List Sem}
    (hok : dm.RecLeafOk d r) (hc : c < d.ctors.length) (h : FitsM dm.sig d r c 0 (arity d c) [] F) :
    ∀ i f, F[i]? = some f → f ∈ₛ[dm.read] dm.fieldTyR d r c i (F.take i) := by
  intro i f hf
  have hfit := DataModel.fitsM_get dm.sig d r c _ 0 [] F h i f hf
  simp only [Nat.zero_add, List.nil_append] at hfit
  have hlen := fitsM_length dm.sig d r c _ 0 [] F h
  have hi : i < F.length := (List.getElem?_eq_some_iff.1 hf).1
  exact fits_mem_fieldTy dm hok hc (hlen ▸ hi) (by simp; omega) hfit

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem propU_congr {P : Value} {p q : Prop} (h : PropU K ρ φ P p) (e : p = q) : PropU K ρ φ P q := e ▸ h

/-- `mkAnd` means conjunction (the unit laws drop a `True` conjunct). -/
theorem propU_mkAnd (hl : LibOk K ρ φ) {P Q : Value} {p q : Prop} (hP : PropU K ρ φ P p)
    (hQ : PropU K ρ φ Q q) : PropU K ρ φ (Ochr.mkAnd P Q) (p ∧ q) := by
  unfold Ochr.mkAnd
  split
  · have e : p = True := prop_inj' ((hP (.plain TyM.err)).symm.trans (hl.tru _))
    subst e
    exact propU_congr hQ (propext ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)
  · have e : q = True := prop_inj' ((hQ (.plain TyM.err)).symm.trans (hl.tru _))
    subst e
    exact propU_congr hP (propext ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
  · exact hl.and _ _ p q hP hQ

theorem propU_andList_nil (hl : LibOk K ρ φ) : PropU K ρ φ (andList []) True := fun h => hl.tru h

theorem propU_andList_cons (hl : LibOk K ρ φ) {P : Value} {Ps : List Value} {p q : Prop}
    (hP : PropU K ρ φ P p) (hQ : PropU K ρ φ (andList Ps) q) : PropU K ρ φ (andList (P :: Ps)) (p ∧ q) := by
  cases Ps with
  | nil =>
    have e : q = True := prop_inj' ((hQ (.plain TyM.err)).symm.trans (hl.tru _))
    subst e
    exact propU_congr hP (propext ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)
  | cons P' Ps' => exact propU_mkAnd hl hP hQ

/-- A constructor value that is a member of a type: the tree, its record the type's, its constructor
one of the declaration's, its fields fitting the telescope of the type's declaration. -/
theorem ind_mem_tree {T : TyM} {t : String} {c : Nat} {hh : Hint} {ps fs : List Value} {h : TyS}
    (nv : NoProp K (.ind t c hh ps fs)) (hm : meanV K ρ φ h (.ind t c hh ps fs) ∈ₛ[K.dm.read] T) :
    ∃ d r d₁, K.Γ.find? (·.name == t) = some d ∧ T.dataCode? = some (d₁, r) ∧ d₁.name = t ∧
      c < d₁.ctors.length ∧
      meanV K ρ φ h (.ind t c hh ps fs) = .dat t r c (meanFields K ρ φ d r c 0 [] fs) ∧
      FitsM K.dm.sig d₁ r c 0 (arity d₁ c) [] (meanFields K ρ φ d r c 0 [] fs) := by
  obtain ⟨d, r, d₁, hd, hT, hn, he, hF⟩ := ind_fit_tree nv (.inr (.inl hm))
  rw [he] at hm
  obtain ⟨d₃, hT₃, hmem, -⟩ := mem_dat_inv K.dm hm
  rw [hT] at hT₃
  simp only [Option.some.injEq, Prod.mk.injEq] at hT₃
  obtain ⟨rfl, -⟩ := hT₃
  obtain ⟨⟨c', hc'⟩, fs', he', -⟩ := (DataLib.mem_iff K.dm.sig d₁ r _).1 hmem
  simp only [Sem.dat.injEq] at he'
  obtain ⟨-, -, hcc, -⟩ := he'
  exact ⟨d, r, d₁, hd, hT, hn, by rw [hcc]; exact hc', he, hF⟩

/-- A constructor value's meaning is never a number. -/
theorem ind_not_num {h : TyS} {t : String} {c : Nat} {hh : Hint} {ps fs : List Value} {n : Nat} :
    meanV K ρ φ h (.ind t c hh ps fs) ≠ .el0 Nat n := by
  intro e
  rcases meanV_ind_cases K ρ φ h t c hh ps fs with e' | ⟨d, r, -, e'⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; split at e <;> cases e

/-- **[Eq-disj] is sound on sides that hold no code**: two sides headed by distinct constructors of one
inductive (or `Z` and `S`), each a member of the equation's type (neither is `⊥`), mean differently.
Assumes nothing beyond the sides' `NoProp` (a constructor value of a `Prop` declaration means `•`,
and two proofs are equal). -/
theorem disj_fo_absurd {T : TyM} {a b : Value} (hd : distinctCtors a b = true)
    (na : NoProp K a) (nb : NoProp K b)
    (sa : SideOkV K ρ φ T a) (sb : SideOkV K ρ φ T b)
    (e : meanV K ρ φ (.plain T) a = meanV K ρ φ (.plain T) b) : False := by
  cases a with
  | zero =>
    cases b with
    | succ b' =>
      obtain ⟨m, hm⟩ := side_succ_num sb
      have e' : Sem.el0 Nat 0 = (meanV K ρ φ (.plain TyM.nat) b').succ := e
      rw [hm, sem_succ_el0] at e'
      cases e'
    | _ => simp [distinctCtors] at hd
  | succ a' =>
    cases b with
    | zero =>
      obtain ⟨n, hn⟩ := side_succ_num sa
      have e' : (meanV K ρ φ (.plain TyM.nat) a').succ = Sem.el0 Nat 0 := e
      rw [hn, sem_succ_el0] at e'
      cases e'
    | _ => simp [distinctCtors] at hd
  | ind t c hh ps fs =>
    cases b with
    | ind u c' hh' qs gs =>
      simp only [distinctCtors, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
      obtain ⟨rfl, hc⟩ := hd
      rcases sa with ha | ha
      · cases ha
      rcases sb with hb | hb
      · cases hb
      obtain ⟨_, _, _, _, _, _, _, ea, _⟩ := ind_mem_tree na ha
      obtain ⟨_, _, _, _, _, _, _, eb, _⟩ := ind_mem_tree nb hb
      rw [ea, eb] at e
      simp only [Sem.dat.injEq] at e
      exact hc e.2.2.1
    | _ => simp [distinctCtors] at hd
  | _ => simp [distinctCtors] at hd

end

theorem meanParams_length (K : RunCtx) (ρ : Assignment) (φ : Future) (d : IndDecl) :
    ∀ (i : Nat) (e : List Sem) (as : List Value), (meanParams K ρ φ d i e as).length = as.length
  | _, _, [] => rfl
  | i, e, a :: as => by
    show (_ :: meanParams K ρ φ d (i + 1) _ as).length = _
    simp [meanParams_length K ρ φ d (i + 1) _ as]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {G : Premises} {gs0 : List GDef} {Γ : List IndDecl}

mutual
/-- **`Eq` computes soundly on sides that hold no code** (constructor values included): if
`Eq(A, a, b)` computes to `P` by the rules (the machine's instance), its sides hold no code and no
`Prop` constructor value, are each `⊥` or a member of `⟦A⟧`, and `⟦A⟧` has a level, then `P` means
`⟦a⟧ = ⟦b⟧` at `⟦A⟧`, at every hint. Assumes [Conv-fun]'s premise (for [Eq-refl]), the unit laws, the
library's connectives, the restated field types (`FieldTysOk`), records without junk leaves at typed
parameters (`LeafsOk`), and that the rules' declarations are the context's (`hΓ`). -/
theorem eqTo_fo (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ FO) (hl : LibOk K ρ φ)
    (hf : FieldTysOk K ρ φ G) (hlf : LeafsOk K Γ)
    (hΓ : ∀ t d, Γ.find? (·.name == t) = some d → K.Γ.find? (·.name == t) = some d) :
    ∀ {A a b P : Value}, EqTo Syn.machine G gs0 Γ A a b P → FO a → FO b → NoProp K a → NoProp K b →
      SideOkV K ρ φ (capTy K ρ φ A) a → SideOkV K ρ φ (capTy K ρ φ A) b →
      (capTy K ρ φ A).level.isSome = true →
      PropU K ρ φ P (meanV K ρ φ (.plain (capTy K ρ φ A)) a = meanV K ρ φ (.plain (capTy K ρ φ A)) b)
  | A, a, b, _, .disjBot hne, _, _, _, _, sa, sb, _ => fun hint => by
    rw [hl.fls hint]
    congr 2
    refine propext ⟨False.elim, fun e => ?_⟩
    by_cases hab : a = .bot
    · have hb : b ≠ .bot := by
        intro hb'; apply hne; show Value.beq a .bot = Value.beq b .bot
        rw [(beq_bot_iff a).2 hab, (beq_bot_iff b).2 hb']
      rcases sb with hb' | hb'
      · exact hb hb'
      · subst hab; exact mem_ne_moved hb' (e.symm.trans rfl)
    · rcases sa with ha' | ha'
      · exact hab ha'
      · have hb : b = .bot := by
          refine Classical.byContradiction fun hnb => ?_
          apply hne; show Value.beq a .bot = Value.beq b .bot
          cases e1 : Value.beq a .bot <;> cases e2 : Value.beq b .bot
          · rfl
          · exact absurd ((beq_bot_iff b).1 e2) hnb
          · exact absurd ((beq_bot_iff a).1 e1) hab
          · rfl
        subst hb; exact mem_ne_moved ha' (e.trans rfl)
  | _, _, _, _, .refl d, pa, pb, na, nb, sa, sb, _ => fun hint => by
    rw [hl.tru hint, convV_alike_fo hp hu d pa pb _ _ na nb (fit_of_sideV sa) (fit_of_sideV sb)]
    congr 2
    exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  | A, .succ a', .succ b', P, .succ d, .succ pa, .succ pb, na, nb, sa, sb, _ => by
    obtain ⟨n, hn⟩ := side_succ_num sa
    obtain ⟨m, hm⟩ := side_succ_num sb
    have ih := eqTo_fo hp hu hl hf hlf hΓ d pa pb na nb (side_of_num hn) (side_of_num hm) rfl
    intro hint
    rw [ih hint]
    congr 2
    show (meanV K ρ φ (.plain TyM.nat) a' = meanV K ρ φ (.plain TyM.nat) b') =
      ((meanV K ρ φ (.plain TyM.nat) a').succ = (meanV K ρ φ (.plain TyM.nat) b').succ)
    rw [hn, hm, sem_succ_el0, sem_succ_el0]
    exact propext ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  | _, _, _, _, @EqTo.inj _ _ _ _ A t c hh hh' ps qs fs gs' args Ts Ps d hargs hd hlen hdep hG hTs heqL,
      .ind pfs, .ind pgs, na, nb, sa, sb, hA => by
    obtain rfl := eqArgs_ind hargs
    have hdK := hΓ t d hd
    rcases meanV_tInd_cases K ρ φ (.plain .err) t args with he | ⟨d', hd', hpk⟩
    · exfalso
      have : capTy K ρ φ (.tInd t args) = TyM.err := by unfold capTy; rw [he]; rfl
      rw [this] at hA; simp [TyM.err, TyM.level, Code0.level] at hA
    rw [hdK] at hd'
    cases hd'
    have hs : (d.sort == 0) = false := by have := na.1 d hdK; simpa using this
    have hcap : capTy K ρ φ (.tInd t args) = K.dm.tyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) := by
      unfold capTy
      simp only [meanV, hdK]
      rw [if_pos hpk]
      rfl
    have hcode : (K.dm.tyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args))).dataCode? =
        some (d, K.dm.recOf d (meanParams K ρ φ d 0 [] args)) := by
      simp [DataModel.tyR, hs, TyM.dataCode?, Code0.dataCode?]
    rw [hcap] at sa sb ⊢
    rcases sa with ha | ha
    · cases ha
    rcases sb with hb | hb
    · cases hb
    obtain ⟨d0, ra, d₁, hd0, hT, -, hc, ea, hFa⟩ := ind_mem_tree na ha
    obtain ⟨d0', rb, d₂, hd0', hT', -, -, eb, hFb⟩ := ind_mem_tree nb hb
    rw [hdK] at hd0 hd0'
    cases hd0
    cases hd0'
    rw [hcode] at hT hT'
    simp only [Option.some.injEq, Prod.mk.injEq] at hT hT'
    obtain ⟨rfl, rfl⟩ := hT
    obtain ⟨rfl, rfl⟩ := hT'
    rw [ea, eb]
    have hleaf : K.dm.RecLeafOk d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) :=
      hlf t d hd _ (by rw [meanParams_length]; exact hf.len d args c fs Ts hG) (paramsTyped_of_ok hpk)
    have hidx : ∀ (k : Nat) (f g : Value), 0 + k ∈ d.indexFields c → fs[k]? = some f → gs'[k]? = some g →
        Alike K ρ φ f g := by
      intro k f g hk hf' hg'
      have hdepc : d.dependent c = true := by
        unfold IndDecl.dependent
        cases hx : d.indexFields c with
        | nil => rw [hx] at hk; simp at hk
        | cons _ _ => rfl
      have hconv := hdep hdepc k (by simpa using hk)
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hf', hg'] at hconv
      exact convV_alike_fo hp hu hconv (pfs f (List.mem_of_getElem? hf')) (pgs g (List.mem_of_getElem? hg'))
    have hTs' : ∀ (k : Nat) (T : Value), Ts[k]? = some T →
        capTy K ρ φ T = K.dm.fieldTyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c (0 + k)
          ([] ++ (meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs).take k) ∧
        (capTy K ρ φ T).level.isSome = true := by
      intro k T hk
      obtain ⟨e1, e2⟩ := hf.sound d args c fs Ts hG hpk k T hk
        (fun i f _ hfi => fitsM_typed K.dm hleaf hc hFa i f hfi)
      simp only [Nat.zero_add, List.nil_append]
      exact ⟨e1, e2⟩
    have hL := eqL_fo hp hu hl hf hlf hΓ heqL 0 (arity d c) [] [] hleaf hc (by simp) rfl rfl
      (by simp) hidx pfs pgs na.2 nb.2 (by simpa using hFa) (by simpa using hFb) hTs'
    exact propU_congr hL (propext ⟨fun h => by rw [h], fun h => by injection h⟩)
  | A, a, b, _, .disj hd, _, _, na, nb, sa, sb, _ => fun hint => by
    rw [hl.fls hint]
    congr 2
    exact propext ⟨False.elim, fun e => disj_fo_absurd hd na nb sa sb e⟩
  | A, a, b, _, .stuck, _, _, _, _, sa, sb, hA => fun hint => by
    rw [meanV_tEq', if_pos ⟨hA, sideOk_of_sideV sa, sideOk_of_sideV sb⟩]

/-- **The field equations mean the equality of the fields**, walking the two telescopes together:
the hints agree while the index fields do (D64: [Eq-inj] takes a dependent constructor apart only
while its index fields are convertible, hence alike, hence equal), each field is a member of the
type its equation is at (it fits the telescope at a record without junk leaves), and each equation
is sound by `eqTo_fo`. -/
theorem eqL_fo (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ FO) (hl : LibOk K ρ φ)
    (hf : FieldTysOk K ρ φ G) (hlf : LeafsOk K Γ)
    (hΓ : ∀ t d, Γ.find? (·.name == t) = some d → K.Γ.find? (·.name == t) = some d) {d : IndDecl} {r : Rec}
    {c : Nat} :
    ∀ {Ts fs gs Ps : List Value}, EqL Syn.machine G gs0 Γ Ts fs gs Ps →
    ∀ (i n : Nat) (ea eb : List Sem), K.dm.RecLeafOk d r → c < d.ctors.length → i + n = arity d c →
      ea.length = i → eb.length = i → (∀ k ∈ d.indexFields c, k < ea.length → ea[k]? = eb[k]?) →
      (∀ (k : Nat) (f g : Value), i + k ∈ d.indexFields c → fs[k]? = some f → gs[k]? = some g →
        Alike K ρ φ f g) →
      (∀ f ∈ fs, FO f) → (∀ g ∈ gs, FO g) → NoPropL K fs → NoPropL K gs →
      FitsM K.dm.sig d r c i n (ea.map Sem.small) (meanFields K ρ φ d r c i ea fs) →
      FitsM K.dm.sig d r c i n (eb.map Sem.small) (meanFields K ρ φ d r c i eb gs) →
      (∀ (k : Nat) (T : Value), Ts[k]? = some T →
        capTy K ρ φ T = K.dm.fieldTyR d r c (i + k) (ea ++ (meanFields K ρ φ d r c i ea fs).take k) ∧
        (capTy K ρ φ T).level.isSome = true) →
      PropU K ρ φ (andList Ps) (meanFields K ρ φ d r c i ea fs = meanFields K ρ φ d r c i eb gs)
  | _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    propU_congr (propU_andList_nil hl) (propext ⟨fun _ => rfl, fun _ => trivial⟩)
  | _, _, _, _, @EqL.cons _ _ _ _ T f g P Ts fs gs Ps hT hrest, i, n, ea, eb, hok, hc, hn, hla, hlb, hag,
      hidx, pfs, pgs, nfs, ngs, hFa, hFb, hTs => by
    obtain ⟨nf, nfs'⟩ := nfs
    obtain ⟨ng, ngs'⟩ := ngs
    have pf : FO f := pfs f (List.mem_cons_self ..)
    have pg : FO g := pgs g (List.mem_cons_self ..)
    have hH : K.dm.fieldTyR d r c i eb = K.dm.fieldTyR d r c i ea :=
      fieldTyIdx K d r c i eb ea (by rw [hla, hlb]) (fun k hk hk' => (hag k hk (by omega)).symm)
    have hT0 : capTy K ρ φ T = K.dm.fieldTyR d r c i ea ∧ (capTy K ρ φ T).level.isSome = true := by
      have := hTs 0 T rfl
      simpa using this
    have hTtail : ∀ (k : Nat) (T' : Value), Ts[k]? = some T' →
        capTy K ρ φ T' = K.dm.fieldTyR d r c (i + 1 + k)
          ((ea ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f]) ++
            (meanFields K ρ φ d r c (i + 1) (ea ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f]) fs).take k) ∧
        (capTy K ρ φ T').level.isSome = true := by
      intro k T' hk
      obtain ⟨e1, e2⟩ := hTs (k + 1) T' (by simpa using hk)
      refine ⟨?_, e2⟩
      rw [e1, show i + (k + 1) = i + 1 + k by omega]
      show K.dm.fieldTyR d r c (i + 1 + k) (ea ++ (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f ::
          meanFields K ρ φ d r c (i + 1) (ea ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f]) fs).take (k + 1)) = _
      simp [List.take_succ_cons]
    have hFa' : FitsM K.dm.sig d r c i n (ea.map Sem.small)
        (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f ::
          meanFields K ρ φ d r c (i + 1) (ea ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f]) fs) := hFa
    have hFb' : FitsM K.dm.sig d r c i n (eb.map Sem.small)
        (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i eb)) g ::
          meanFields K ρ φ d r c (i + 1) (eb ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i eb)) g]) gs) := hFb
    have ihT := eqTo_fo hp hu hl hf hlf hΓ hT pf pg nf ng
    show PropU K ρ φ (andList (P :: Ps))
      (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f ::
          meanFields K ρ φ d r c (i + 1) (ea ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f]) fs =
        meanV K ρ φ (.plain (K.dm.fieldTyR d r c i eb)) g ::
          meanFields K ρ φ d r c (i + 1) (eb ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i eb)) g]) gs)
    rw [hH] at hFb' ⊢
    rw [hT0.1] at ihT
    generalize hx : meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f = x at hFa' hTtail ihT ⊢
    generalize hy : meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) g = y at hFb' ihT ⊢
    cases n with
    | zero => exact absurd hFa' (by simp [FitsM])
    | succ n =>
    obtain ⟨x0, xs0, hxs, h1, h2⟩ := hFa'
    obtain ⟨y0, ys0, hys, k1, k2⟩ := hFb'
    simp only [List.cons.injEq] at hxs hys
    obtain ⟨rfl, rfl⟩ := hxs
    obtain ⟨rfl, rfl⟩ := hys
    have hxm : x ∈ₛ[K.dm.read] K.dm.fieldTyR d r c i ea := fits_mem_fieldTy K.dm hok hc (by omega) hla h1
    have hym : y ∈ₛ[K.dm.read] K.dm.fieldTyR d r c i ea := by
      rw [← hH]; exact fits_mem_fieldTy K.dm hok hc (by omega) hlb k1
    have ihT' := ihT
      (.inr (show meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) f ∈ₛ[K.dm.read] _ by rw [hx]; exact hxm))
      (.inr (show meanV K ρ φ (.plain (K.dm.fieldTyR d r c i ea)) g ∈ₛ[K.dm.read] _ by rw [hy]; exact hym)) (hT0.1 ▸ hT0.2)
    have hag' : ∀ k ∈ d.indexFields c, k < (ea ++ [x]).length → (ea ++ [x])[k]? = (eb ++ [y])[k]? := by
      intro k hk hlt
      by_cases hki : k < ea.length
      · rw [List.getElem?_append_left hki, List.getElem?_append_left (by omega)]
        exact hag k hk hki
      · have hk' : k = i := by simp at hlt; omega
        subst hk'
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [hla, hlb, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
        have hal := hidx 0 f g (by simpa using hk) rfl rfl
        rw [← hx, ← hy]
        exact hal _ _ nf ng (.inr (.inl (hx ▸ hxm))) (.inr (.inl (hy ▸ hym)))
    have ihL := eqL_fo hp hu hl hf hlf hΓ hrest (i + 1) n (ea ++ [x]) (eb ++ [y]) hok hc (by omega)
      (by simp [hla]) (by simp [hlb]) hag'
      (fun k f' g' hk hf' hg' => hidx (k + 1) f' g' (by rwa [show i + (k + 1) = i + 1 + k by omega]) hf' hg')
      (fun a ha => pfs a (List.mem_cons_of_mem _ ha)) (fun a ha => pgs a (List.mem_cons_of_mem _ ha)) nfs' ngs'
      (by simpa using h2) (by simpa using k2) hTtail
    exact propU_congr (propU_andList_cons hl ihT' ihL) (List.cons.injEq _ _ _ _).symm
end

end

end Ochr.Meaning.Conv
