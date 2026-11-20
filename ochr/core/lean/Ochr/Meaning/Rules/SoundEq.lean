import Ochr.Meaning.Rules.SoundT

/-!
# The rules trial, part A for `Eq` under the typing predicate: `Eq` computes soundly

`EqTo A a b P` ("`Eq(A, a, b)` computes to `P`", `Rules/Conv.lean`) in the machine's instance: the
proposition `P` means `⟦a⟧ = ⟦b⟧` at `⟦A⟧`. What each side must be, named so that it is visibly
what the evaluation of the side and the checker's typing of it will supply:

- `SideMem`: `⊥`, or a whole member of `⟦A⟧` (D84: a side is moved on every path or whole). Its
  membership half is what the evaluation step will conclude (`Rules/InFlight.lean`,
  `EvalMemConcl`) together with the check of the side's type against `A` (`eqChecks`);
- `HWT ⟦A⟧`: well typed inside (the typing gap);
- `Q`: the class `CodeOk` holds on.

What A takes as given beyond conversion's hypotheses, each named: the library's `True`, `False`,
`And` (`LibOkT`); [Eq-inj]'s field types (`FieldTysSound`: the abstract premise's soundness; in the
machine's instance, `fieldTypesOf` computes the model's field types, under the assignment after
the computation, since in the inherent-growth case a field type names an unknown it made); and a
fact of the data model (`FieldTyIdx`: a field's type reads only the fields the declaration's field
types mention, D64's index fields).
-/

namespace Ochr.Meaning.Rules
open Ochr Ochr.Meaning Ochr.Meaning.Steps

theorem prop_inj {p q : Prop} (h : TyM.prop p = TyM.prop q) : p = q := by
  unfold TyM.prop at h
  injection h with hA hc
  exact Code0.congr_heq Code0.propOf _ _ hA hc

theorem beq_bot_iff (a : Value) : Value.beq a .bot = true ↔ a = .bot := by
  cases a <;> simp [Value.beq]

theorem sem_succ_ne_zero (x : Sem) : x.succ ≠ .el0 Nat 0 := by
  unfold Sem.succ
  split
  · simp
  · split <;> simp

theorem sem_succ_ne_moved (x : Sem) : x.succ ≠ .moved := by
  unfold Sem.succ
  split
  · simp
  · split <;> simp

/-- A whole successor is the successor of a number. -/
theorem sem_succ_whole {x : Sem} (h : x.succ.whole) : ∃ n, x = .el0 Nat n := by
  unfold Sem.succ at h
  split at h
  · rename_i n hn
    unfold Sem.asNat Sem.as at hn
    split at hn
    · rename_i B b
      split at hn
      · rename_i e; subst e; cases hn; exact ⟨_, rfl⟩
      · cases hn
    · cases hn
  · split at h
    · simp [Sem.whole] at h
    · rename_i hw
      simp only [Sem.whole, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at h
      exact absurd h hw

/-- The choice of parameters [Eq-inj] reads the field types at. -/
theorem eqArgs_cases {A : Value} {t : String} {ps qs args : List Value} (h : eqArgs A t ps qs = some args) :
    (∃ as, A = .tInd t as ∧ args = as) ∨ (ps ≠ [] ∧ args = ps) ∨ (qs ≠ [] ∧ args = qs) := by
  unfold eqArgs at h
  have tail : ((fun _ : Unit => if (!ps.isEmpty) = true then some ps else if (!qs.isEmpty) = true then some qs else none) ()
      = some args) → (ps ≠ [] ∧ args = ps) ∨ (qs ≠ [] ∧ args = qs) := by
    intro h
    simp only at h
    split at h
    · rename_i hp; cases h; exact .inl ⟨by simpa using hp, rfl⟩
    · split at h
      · rename_i hq; cases h; exact .inr ⟨by simpa using hq, rfl⟩
      · cases h
  cases A with
  | tInd n as =>
    simp only at h
    split at h
    · rename_i hn
      simp only [Option.orElse_some, Option.some.injEq] at h
      simp only [beq_iff_eq] at hn
      subst hn; subst h
      exact .inl ⟨_, rfl, rfl⟩
    · exact .inr (tail h)
  | _ => exact .inr (tail h)

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The library's propositions mean what they say, stated for arguments whose meaning does not
depend on the hint they are read at (`Rules/Sound.lean`'s `LibOk.and` asked it of arguments
meaning propositions at hint `err`, while `D(ā)` reads its arguments at the parameter types). -/
structure LibOkT : Prop where
  tru : ∀ hint, meanV K ρ φ hint vTrue = .ty (TyM.prop True)
  fls : ∀ hint, meanV K ρ φ hint vFalse = .ty (TyM.prop False)
  and : ∀ (P Q : Value) (p q : Prop), (∀ hint, meanV K ρ φ hint P = .ty (TyM.prop p)) →
    (∀ hint, meanV K ρ φ hint Q = .ty (TyM.prop q)) →
    ∀ hint, meanV K ρ φ hint (.tInd "And" [P, Q]) = .ty (TyM.prop (p ∧ q))

/-- [Eq-inj]'s abstract premise is sound: each computed field type means the model's field type at
the record of the parameters and the left side's earlier fields. -/
def FieldTysSound (G : Premises) : Prop :=
  ∀ d args c fs Ts, G.fieldTys d args c fs Ts → ∀ j T, Ts[j]? = some T →
    tyOf K ρ φ T = K.dm.fieldTyR d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c j
      ((meanFields K ρ φ d (K.dm.recOf d (meanParams K ρ φ d 0 [] args)) c 0 [] fs).take j)

/-- A fact of the data model (D64): a field's type reads, of the earlier fields, only the index
fields (those some field type of the declaration mentions). -/
def FieldTyIdx : Prop :=
  ∀ d r c j (e e' : List Sem), e.length = e'.length →
    (∀ k ∈ d.indexFields c, k < e.length → e[k]? = e'[k]?) →
    K.dm.fieldTyR d r c j e = K.dm.fieldTyR d r c j e'

/-- **A side of an `Eq`** (D84): `⊥`, or a whole member of the equation's type. -/
def SideMem (T : TyM) (a : Value) : Prop :=
  a = .bot ∨ ((meanV K ρ φ (.plain T) a).whole ∧ meanV K ρ φ (.plain T) a ∈ₛ[K.dm.read] T)

theorem SideMem.ne_moved {T : TyM} {a : Value} (h : SideMem K ρ φ T a) (hb : a ≠ .bot) :
    meanV K ρ φ (.plain T) a ≠ .moved := by
  rcases h with rfl | ⟨hw, -⟩
  · exact absurd rfl hb
  · intro e; rw [e] at hw; simp [Sem.whole] at hw

/-- A meaning uniform over hints. -/
def PropU (P : Value) (p : Prop) : Prop := ∀ hint, meanV K ρ φ hint P = .ty (TyM.prop p)

/-- The conjunction `andList` builds (with the unit laws) means the conjunction of its parts. -/
theorem andList_mean (hl : LibOkT K ρ φ) : ∀ (Ps : List Value) (ps : List Prop),
    Fa2 (PropU K ρ φ) Ps ps → PropU K ρ φ (andList Ps) (∀ p ∈ ps, p)
  | [], [], .nil => fun hint => by
    rw [show andList [] = vTrue from rfl, hl.tru hint]
    congr 2; exact propext ⟨fun _ _ h => (List.not_mem_nil h).elim, fun _ => trivial⟩
  | [P], [p], .cons h .nil => fun hint => by
    rw [show andList [P] = P from rfl, h hint]
    congr 2; exact propext ⟨fun hp x hx => by rw [List.mem_singleton.1 hx]; exact hp, fun h => h p (List.mem_singleton_self p)⟩
  | P :: P' :: Ps, p :: p' :: ps, .cons h (.cons h' hs) => by
    have ih := andList_mean hl (P' :: Ps) (p' :: ps) (.cons h' hs)
    have e : andList (P :: P' :: Ps) = mkAnd P (andList (P' :: Ps)) := rfl
    have goal : (∀ x ∈ p :: p' :: ps, x) = (p ∧ ∀ x ∈ p' :: ps, x) := by
      exact propext List.forall_mem_cons
    intro hint
    rw [e, goal]
    unfold mkAnd
    split
    · have hp : True = p := prop_inj (Sem.ty.inj ((hl.tru hint).symm.trans (h hint)))
      rw [ih hint, ← hp, true_and]
    · rename_i heq
      have hq : True = (∀ x ∈ p' :: ps, x) := by
        have := ih hint; rw [heq] at this
        exact prop_inj (Sem.ty.inj ((hl.tru hint).symm.trans this))
      rw [h hint, ← hq, and_true]
    · exact hl.and _ _ _ _ h ih hint

/-- A well-typed value is a (partly moved) member of its type. -/
theorem HWT.pmem' : ∀ {T : TyM} {v : Value}, HWT K ρ φ T v →
    DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) v) T
  | _, _, .atom _ h => h
  | _, _, .succ h _ => h
  | _, _, .tEq h _ _ _ => h
  | _, _, .tInd h _ _ => h
  | _, _, .ind h _ _ _ _ _ => h
  | _, _, .tRef h _ => h
  | _, _, .borrow h => by simp only [meanV]; exact HWT.pmem' h
  | _, _, .gloan h => by simp only [meanV]; exact HWT.pmem' h
  | _, _, .sealed h _ => h
  | _, _, .clo h _ _ => h
  | _, _, .tPi h _ _ => h

/-- A field that fits its shape among the members and is a partly moved member of the shape's
type is a whole member of it. -/
theorem field_mem {s : Sem} {sh : DataLib.Shape} (hfit : DataLib.FitsOneM K.dm.sig sh s)
    (hp : DataModel.pmem K.dm.read K.Γ s (K.dm.shapeTy sh)) :
    s.whole ∧ s ∈ₛ[K.dm.read] K.dm.shapeTy sh := by
  have hw : s.whole := by
    cases sh with
    | leaf B c => obtain ⟨b, rfl⟩ := hfit; exact DataLib.encLeaf_whole c b
    | sub d r => exact DataLib.mem_whole K.dm.sig d r s hfit
    | prf d r => obtain ⟨rfl, -⟩ := hfit; simp [Sem.whole]
  refine ⟨hw, K.dm.fitsOneM_mem sh s hfit fun he => ?_⟩
  rw [he] at hp
  rcases hp with rfl | ⟨t, -, -, hin | ho⟩
  · simp [Sem.whole] at hw
  · exact DataModel.err_mem_false _ _ hin
  · exact ho

/-- A constructor value that is a member of a data type has fields fitting their shapes. -/
theorem fitsM_of_mem {d : IndDecl} {r : Rec} {t : String} {c : Nat} {ms : List Sem}
    (hs : (d.sort == 0) = false) (h : Sem.dat t r c ms ∈ₛ[K.dm.read] K.dm.tyR d r) :
    DataLib.FitsM K.dm.sig d r c 0 (DataLib.arity d c) [] ms := by
  obtain ⟨c', fs', e, hf⟩ := (DataLib.mem_iff K.dm.sig d r _).1 ((K.dm.mem_tyR d r hs _).1 h)
  cases e
  exact hf

/-- With parameters recorded, a well-typed constructor value's record is theirs. -/
theorem pinned_rec_ps {T : TyM} {t : String} {c : Nat} {h : Hint} {ps fs : List Value} {d : IndDecl}
    {r : Rec} (hm : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain T) (.ind t c h ps fs)) T)
    (hd : K.Γ.find? (·.name == t) = some d) (hs : (d.sort == 0) = false) (hT : T = K.dm.tyR d r)
    (hps : ps ≠ []) : K.dm.recOf d (meanParams K ρ φ d 0 [] ps) = r := by
  have he : ps.isEmpty = false := by cases ps; exact absurd rfl hps; rfl
  revert hm
  simp only [meanV, hd, he, Bool.false_and, Bool.false_eq_true, reduceIte, hs, DataModel.ctorR]
  intro hm
  subst hT
  exact pmem_dat_rec K hs hm

end

/-- Everything A takes as given, bundled: conversion's (`Closed`, `PremSoundT`, `UnitOk`,
`CodeOk`) and `Eq`'s (`LibOkT`, `FieldTysSound`, `FieldTyIdx`). -/
structure AHyps (K : RunCtx) (ρ : Assignment) (φ : Future) (Q : Value → Prop) (G : Premises)
    (gs₀ : List GDef) : Prop where
  closed : Closed Q
  prem : PremSoundT K ρ φ G
  unit : UnitOk K ρ φ Q
  code : CodeOk K ρ φ Q G gs₀
  lib : LibOkT K ρ φ
  fieldTys : FieldTysSound K ρ φ G
  idx : FieldTyIdx K

theorem sem_succ_el0 (n : Nat) : (Sem.el0 Nat n).succ = .el0 Nat (n + 1) := by
  simp [Sem.succ, Sem.asNat, Sem.as]

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {Q : Value → Prop} {G : Premises} {gs₀ : List GDef}

mutual
/-- **(A) `Eq` computes soundly** (handoff step 8): if `Eq(A, a, b)` computes to `P` by the rules
(machine's instance), and each side is well typed at `⟦A⟧` and `⊥` or a whole member of it, then
`P` means `⟦a⟧ = ⟦b⟧` at `⟦A⟧`, at every hint. -/
theorem eqTo_alike (H : AHyps K ρ φ Q G gs₀) : ∀ {A a b P : Value}, EqTo Syn.machine G gs₀ K.Γ A a b P →
    Q a → Q b → HWT K ρ φ (tyOf K ρ φ A) a → HWT K ρ φ (tyOf K ρ φ A) b →
    SideMem K ρ φ (tyOf K ρ φ A) a → SideMem K ρ φ (tyOf K ρ φ A) b →
    PropU K ρ φ P (meanV K ρ φ (.plain (tyOf K ρ φ A)) a = meanV K ρ φ (.plain (tyOf K ρ φ A)) b)
  | A, a, b, _, .disjBot hne, _, _, _, _, sa, sb => fun hint => by
    rw [H.lib.fls hint]
    congr 2
    have ha := beq_bot_iff a
    have hb := beq_bot_iff b
    by_cases hab : a = .bot
    · have hb' : b ≠ .bot := by
        intro e; apply hne; show Value.beq a .bot = Value.beq b .bot
        rw [ha.2 hab, hb.2 e]
      have := SideMem.ne_moved K ρ φ sb hb'
      subst hab
      exact propext ⟨False.elim, fun h => this (by simp only [meanV] at h; exact h.symm)⟩
    · have hb' : b = .bot := by
        refine Classical.byContradiction fun hnb => ?_
        apply hne; show Value.beq a .bot = Value.beq b .bot
        cases e1 : Value.beq a .bot <;> cases e2 : Value.beq b .bot
        · rfl
        · exact absurd (hb.1 e2) hnb
        · exact absurd (ha.1 e1) hab
        · rfl
      have := SideMem.ne_moved K ρ φ sa hab
      subst hb'
      exact propext ⟨False.elim, fun h => this (by simp only [meanV] at h; exact h)⟩
  | A, a, b, _, .refl d, qa, qb, ha, hb, _, _ => fun hint => by
    rw [H.lib.tru hint, (convV_alike H.closed H.prem H.unit H.code d qa qb).1 _ ha hb]
    congr 2
    exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  | A, .succ a', .succ b', P, .succ d, qa, qb, ha, hb, sa, sb => by
    have hta : HWT K ρ φ TyM.nat a' := by
      cases ha with | atom hx _ => exact hx.elim | succ _ h => exact h
    have htb : HWT K ρ φ TyM.nat b' := by
      cases hb with | atom hx _ => exact hx.elim | succ _ h => exact h
    have num : ∀ x, SideMem K ρ φ (tyOf K ρ φ A) (.succ x) → ∃ n, meanV K ρ φ (.plain TyM.nat) x = .el0 Nat n := by
      intro x hx
      rcases hx with hx | ⟨hw, -⟩
      · cases hx
      · simp only [meanV] at hw
        exact sem_succ_whole hw
    obtain ⟨n, hn⟩ := num a' sa
    obtain ⟨m, hm⟩ := num b' sb
    have side : ∀ x k, meanV K ρ φ (.plain TyM.nat) x = .el0 Nat k → SideMem K ρ φ (tyOf K ρ φ .tNat) x :=
      fun x k hk => .inr ⟨by show (meanV K ρ φ (.plain TyM.nat) x).whole; rw [hk]; simp [Sem.whole],
        by show meanV K ρ φ (.plain TyM.nat) x ∈ₛ[K.dm.read] TyM.nat; rw [hk]; exact ⟨k, rfl⟩⟩
    have ih := eqTo_alike H d (H.closed.succ qa) (H.closed.succ qb) hta htb (side a' n hn) (side b' m hm)
    intro hint
    rw [ih hint]
    congr 2
    show (meanV K ρ φ (.plain TyM.nat) a' = meanV K ρ φ (.plain TyM.nat) b') = _
    simp only [meanV]
    rw [hn, hm, sem_succ_el0, sem_succ_el0]
    exact propext ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  | A, .ind t c hh ps fs, .ind _ _ hh' qs gs, _, .inj (d := d) (args := args) hargs hd hlen hidx hft hTl hL, qa, qb, ha, hb, sa, sb => by
    cases ha with
    | atom hx _ => exact hx.elim
    | @ind _ _ _ _ _ _ d1 r hm hd1 hs hT _ hfs =>
    cases hb with
    | atom hx _ => exact hx.elim
    | @ind _ _ _ _ _ _ d2 r' hm' hd2 _ hT' _ hgs =>
    rw [hd] at hd1 hd2
    cases hd1; cases hd2
    have er := tyR_rec_inj K hs (hT.symm.trans hT')
    subst er
    have pa := meanV_ind_pinned K ρ φ hm hd hs hT
    have pb := meanV_ind_pinned K ρ φ hm' hd hs hT'
    have fa : DataLib.FitsM K.dm.sig d r c 0 (DataLib.arity d c) [] (meanFields K ρ φ d r c 0 [] fs) := by
      rcases sa with h0 | ⟨-, hmem⟩
      · cases h0
      · rw [pa, hT] at hmem; exact fitsM_of_mem K hs hmem
    have fb : DataLib.FitsM K.dm.sig d r c 0 (DataLib.arity d c) [] (meanFields K ρ φ d r c 0 [] gs) := by
      rcases sb with h0 | ⟨-, hmem⟩
      · cases h0
      · rw [pb, hT] at hmem; exact fitsM_of_mem K hs hmem
    have hrec : K.dm.recOf d (meanParams K ρ φ d 0 [] args) = r := by
      rcases eqArgs_cases hargs with ⟨as, rfl, rfl⟩ | ⟨hne, rfl⟩ | ⟨hne, rfl⟩
      · refine tyR_rec_inj K hs (Eq.trans ?_ hT)
        simp only [tyOf, meanV, hd, Sem.asTy]; rfl
      · exact pinned_rec_ps K ρ φ hm hd hs hT hne
      · exact pinned_rec_ps K ρ φ hm' hd hs hT' hne
    obtain ⟨pl, hpl, hiff⟩ := fields_alike H hL hfs hgs fa fb (H.closed.ind qa) (H.closed.ind qb) rfl rfl
      (fun _ _ h => absurd h (Nat.not_lt_zero _))
      (fun k hk _ x y hx hy => by
        have hdep : d.dependent c = true := by
          simp only [IndDecl.dependent, Bool.not_eq_true']
          cases e : _root_.Ochr.IndDecl.indexFields _ _ with
          | nil => rw [e] at hk; cases hk
          | cons _ _ => rfl
        have := hidx hdep k hk
        simp only [Nat.sub_zero] at hx hy
        rwa [List.getD_eq_getElem?_getD, hx, List.getD_eq_getElem?_getD, hy] at this)
      (fun j T' hj => by
        rw [H.fieldTys _ _ _ _ _ hft j T' hj, hrec]
        simp)
    intro hint
    rw [andList_mean K ρ φ H.lib _ pl hpl hint, pa, pb]
    congr 2
    exact propext (hiff.trans ⟨fun e => by rw [e], fun e => by injection e⟩)
  | A, a, b, _, .disj hdc, _, _, ha, hb, _, _ => fun hint => by
    rw [H.lib.fls hint]
    congr 2
    refine propext ⟨False.elim, fun h => ?_⟩
    unfold distinctCtors at hdc
    split at hdc
    · simp only [meanV] at h; exact sem_succ_ne_zero _ h.symm
    · simp only [meanV] at h; exact sem_succ_ne_zero _ h
    · rename_i t c _ _ _ u c' _ _ _
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hdc
      obtain ⟨rfl, hcc⟩ := hdc
      cases ha with
      | atom hx _ => exact hx.elim
      | ind hm hd hs hT _ _ =>
        cases hb with
        | atom hx _ => exact hx.elim
        | ind hm' hd' _ hT' _ _ =>
          rw [hd] at hd'; cases hd'
          have er := tyR_rec_inj K hs (hT.symm.trans hT')
          subst er
          rw [meanV_ind_pinned K ρ φ hm hd hs hT, meanV_ind_pinned K ρ φ hm' hd hs hT'] at h
          injection h with _ _ h3 _
          exact hcc h3
    · cases hdc
  | _, _, _, _, .stuck, _, _, _, _, _, _ => fun hint => by
    simp only [meanV, tyOf]

/-- [Eq-inj]'s field equations, field by field: the field types agree on both sides (the index
fields agree, by conversion), and the equations' conjunction holds exactly when the fields' meanings
do. -/
theorem fields_alike (H : AHyps K ρ φ Q G gs₀) :
    ∀ {d : IndDecl} {r : Rec} {c : Nat} {Ts fs gs Ps : List Value} {i n : Nat} {e e' : List Sem},
    EqL Syn.machine G gs₀ K.Γ Ts fs gs Ps →
    HWTFields K ρ φ d r c i e fs → HWTFields K ρ φ d r c i e' gs →
    DataLib.FitsM K.dm.sig d r c i n (e.map Sem.small) (meanFields K ρ φ d r c i e fs) →
    DataLib.FitsM K.dm.sig d r c i n (e'.map Sem.small) (meanFields K ρ φ d r c i e' gs) →
    (∀ a ∈ fs, Q a) → (∀ b ∈ gs, Q b) → e.length = i → e'.length = i →
    (∀ k ∈ d.indexFields c, k < i → e[k]? = e'[k]?) →
    (∀ k ∈ d.indexFields c, i ≤ k → ∀ x y, fs[k - i]? = some x → gs[k - i]? = some y →
      ConvV Syn.machine G gs₀ x y) →
    (∀ j T, Ts[j]? = some T →
      tyOf K ρ φ T = K.dm.fieldTyR d r c (i + j) (e ++ (meanFields K ρ φ d r c i e fs).take j)) →
    ∃ ps : List Prop, Fa2 (PropU K ρ φ) Ps ps ∧
      ((∀ p ∈ ps, p) ↔ meanFields K ρ φ d r c i e fs = meanFields K ρ φ d r c i e' gs)
  | _, _, _, _, _, _, _, _, _, _, _, .nil, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨[], .nil, ⟨fun _ => rfl, fun _ _ h => (List.not_mem_nil h).elim⟩⟩
  | d, r, c, T :: Ts, f :: fs, g :: gs, P :: Ps, i, n, e, e', .cons hT hL, hf, hg, hfit, hgit, qf, qg, hle, hle',
      hag, hcv, hty => by
    cases hf with | cons hf1 hfs =>
    cases hg with | cons hg1 hgs =>
    have hU : K.dm.fieldTyR d r c i e' = K.dm.fieldTyR d r c i e :=
      H.idx d r c i e' e (hle'.trans hle.symm) (fun k hk hlt => (hag k hk (hle' ▸ hlt)).symm)
    have hpg : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e')) g)
        (K.dm.shapeTy (K.dm.sig.shape d r c i (e'.map Sem.small))) := HWT.pmem' K ρ φ hg1
    have hpf : DataModel.pmem K.dm.read K.Γ (meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f)
        (K.dm.shapeTy (K.dm.sig.shape d r c i (e.map Sem.small))) := HWT.pmem' K ρ φ hf1
    rw [hU] at hg1 hgs hpg
    have hTU : tyOf K ρ φ T = K.dm.fieldTyR d r c i e := by simpa using hty 0 T rfl
    have mf : meanFields K ρ φ d r c i e (f :: fs) =
        meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f :: meanFields K ρ φ d r c (i + 1)
          (e ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) f]) fs := rfl
    have mg : meanFields K ρ φ d r c i e' (g :: gs) =
        meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) g :: meanFields K ρ φ d r c (i + 1)
          (e' ++ [meanV K ρ φ (.plain (K.dm.fieldTyR d r c i e)) g]) gs := by
      simp only [meanFields, hU]
    rw [mf] at hfit hty ⊢
    rw [mg] at hgit ⊢
    match n, hfit, hgit with
    | 0, hfit, _ => simp [DataLib.FitsM] at hfit
    | n + 1, ⟨s0, rest, hms, hfo, hrf⟩, ⟨s0', rest', hns, hgo, hrg⟩ =>
      injection hms with e1 e2
      injection hns with e3 e4
      subst e1 e2 e3 e4
      have sf : SideMem K ρ φ (K.dm.fieldTyR d r c i e) f := .inr (field_mem K hfo hpf)
      have sg : SideMem K ρ φ (K.dm.fieldTyR d r c i e) g := by
        have := field_mem K hgo hpg
        exact .inr ⟨this.1, by have h2 := this.2; rwa [show K.dm.shapeTy (K.dm.sig.shape d r c i (e'.map Sem.small)) =
          K.dm.fieldTyR d r c i e' from rfl, hU] at h2⟩
      have qf1 := qf f (List.mem_cons_self ..)
      have qg1 := qg g (List.mem_cons_self ..)
      have ih := eqTo_alike H hT qf1 qg1 (hTU ▸ hf1) (hTU ▸ hg1) (hTU ▸ sf) (hTU ▸ sg)
      rw [hTU] at ih
      obtain ⟨ps, hps, hiff⟩ := fields_alike H hL hfs hgs
        (by rw [List.map_append]; exact hrf) (by rw [List.map_append]; exact hrg)
        (fun a ha => qf a (List.mem_cons_of_mem _ ha)) (fun b hb => qg b (List.mem_cons_of_mem _ hb))
        (by simp [hle]) (by simp [hle'])
        (fun k hk hlt => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | rfl
          · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
            exact hag k hk hlt
          · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hle, hle']
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq]
            exact (convV_alike H.closed H.prem H.unit H.code
              (hcv k hk (Nat.le_refl _) f g (by simp) (by simp)) qf1 qg1).1 _ hf1 hg1)
        (fun k hk hle2 x y hx hy => by
          have e5 : k - i = (k - (i + 1)) + 1 := by omega
          exact hcv k hk (by omega) x y (by rw [e5]; simpa using hx) (by rw [e5]; simpa using hy))
        (fun j T' hj => by
          rw [hty (j + 1) T' (by simpa using hj)]
          congr 1
          · omega
          · simp [List.take_succ_cons])
      exact ⟨_ :: ps, .cons ih hps, by simp only [List.forall_mem_cons, List.cons.injEq, hiff]⟩
end

end

end Ochr.Meaning.Rules


