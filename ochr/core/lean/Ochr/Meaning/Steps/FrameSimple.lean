import Ochr.Meaning.Steps.FramePlace

/-!
# The frame property's remaining clauses: values, statements, annotations, data (lead35; docs/31 D225)

The clauses that make no borrow: constants and literals, embedded values, `S(u)`, `&A` as a type, equalities and their
proofs (statements on copies), annotations, inductive types and constructors. Statements run on a copy of the state and
keep only their value: across the frame relation their runs agree in value (`VAgree`), whatever their labels.
-/

namespace Ochr.Meaning.Steps.Form.FrameEnd

open Ochr Ochr.Meaning Ochr.Meaning.Strict

/-! ## Runs that agree in value -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- Two runs agree up to `E` on their results, from related states. -/
def VAgree (K : RunCtx) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) {α : Type 3} (E : α → α → Prop) :
    Option (α × SState) → Option (α × SState) → Prop
  | some (a, t), some (a', t') => E a a' ∧ FrameInv K φ σ s₀ ks t t'
  | none, none => True
  | _, _ => False

/-- The same value and type; labels forgotten. -/
def ResV (r r' : Res) : Prop := r.1 = r'.1 ∧ r.2.m = r'.2.m

/-- The same result, with no label. -/
def ResN (r r' : Res) : Prop := r = r' ∧ r.2.label = none

theorem vagree_of_agreeI {o o' : Option (Res × SState)} (h : FrameAgreeI K φ σ s₀ ks o o') :
    VAgree K φ σ s₀ ks ResV o o' := by
  match o, o', h with
  | some (r, t), some (r', t'), ⟨h1, h2, h3, _⟩ => exact ⟨⟨h1, by rw [h2]⟩, h3⟩
  | none, none, _ => trivial

theorem agreeI_of_vagree {o o' : Option (Res × SState)} (h : VAgree K φ σ s₀ ks ResN o o') :
    FrameAgreeI K φ σ s₀ ks o o' := by
  match o, o', h with
  | some (r, t), some (r', t'), ⟨⟨e, hl⟩, h3⟩ =>
    subst e
    obtain ⟨v, m, lab⟩ := r
    simp only at hl; subst hl
    exact ⟨rfl, rfl, h3, ⟨fun _ e => (by cases e), fun _ e => (by cases e)⟩⟩
  | none, none, _ => trivial

theorem vagree_onCopy {α : Type 3} {E : α → α → Prop} {x x' : SM α} {s s' : SState} (hI : FrameInv K φ σ s₀ ks s s')
    (h : VAgree K φ σ s₀ ks E (x s) (x' s')) : VAgree K φ σ s₀ ks E (SM.onCopy x s) (SM.onCopy x' s') := by
  unfold SM.onCopy
  match x s, x' s', h with
  | some (a, t), some (a', t'), ⟨e, _⟩ => exact ⟨e, hI⟩
  | none, none, _ => trivial

theorem vagree_bind {α β : Type 3} {E : α → α → Prop} {E₂ : β → β → Prop} {x x' : SM α} {f f' : α → SM β}
    {s s' : SState} (h : VAgree K φ σ s₀ ks E (x s) (x' s'))
    (hf : ∀ a a' t t', E a a' → FrameInv K φ σ s₀ ks t t' → VAgree K φ σ s₀ ks E₂ (f a t) (f' a' t')) :
    VAgree K φ σ s₀ ks E₂ ((x >>= f) s) ((x' >>= f') s') := by
  show VAgree K φ σ s₀ ks E₂ (match x s with | some (a, t) => f a t | none => none)
    (match x' s' with | some (a, t) => f' a t | none => none)
  match x s, x' s', h with
  | some (a, t), some (a', t'), ⟨e, hI⟩ => exact hf a a' t t' e hI
  | none, none, _ => trivial

theorem vagree_pure {α : Type 3} {E : α → α → Prop} {a a' : α} {s s' : SState} (hI : FrameInv K φ σ s₀ ks s s')
    (e : E a a') : VAgree K φ σ s₀ ks E ((pure a : SM α) s) ((pure a' : SM α) s') := ⟨e, hI⟩

/-- A test on the value, the state passed on. -/
theorem vagree_test {α : Type 3} {E : α → α → Prop} {P : Prop} [Decidable P] {a a' : α} {s s' : SState}
    (hI : FrameInv K φ σ s₀ ks s s') (e : E a a') :
    VAgree K φ σ s₀ ks E (if P then some (a, s) else none) (if P then some (a', s') else none) := by
  split
  · exact ⟨e, hI⟩
  · trivial

/-- A run that agrees, as a run that agrees in value. -/
theorem vagree_run {ρ : Assignment} {t : Term} (ih : TermFrame K ρ φ σ s₀ ks t) (tl : Bool) (hint : TyS) {s s' : SState}
    (hI : FrameInv K φ σ s₀ ks s s') : VAgree K φ σ s₀ ks ResV (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s') :=
  vagree_of_agreeI (ih tl hint s s' hI)

end

/-! ## Constants, literals, embedded values -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- A pure result with no label. -/
theorem agreeI_pure {r : Res} (hl : r.2.label = none) {s s' : SState} (hI : FrameInv K φ σ s₀ ks s s') :
    FrameAgreeI K φ σ s₀ ks ((pure r : SM Res) s) ((pure r : SM Res) s') :=
  agreeI_of_vagree ⟨⟨rfl, hl⟩, hI⟩

theorem runFrameI_const (hK : ∀ n, (K.C.global n).2.label = none) (n : String) :
    TermFrame K ρ φ σ s₀ ks (.const n) := fun tl hint s s' hI => by
  rw [runT]; exact agreeI_pure (hK n) hI

theorem runFrameI_sort {l} : TermFrame K ρ φ σ s₀ ks (.sort l) := fun tl hint s s' hI => by
  rw [runT]; exact agreeI_pure rfl hI

theorem runFrameI_nat : TermFrame K ρ φ σ s₀ ks .nat := fun tl hint s s' hI => by
  rw [runT]; exact agreeI_pure rfl hI

theorem runFrameI_unit : TermFrame K ρ φ σ s₀ ks .unit := fun tl hint s s' hI => by
  rw [runT]; exact agreeI_pure rfl hI

theorem runFrameI_zero : TermFrame K ρ φ σ s₀ ks .zero := fun tl hint s s' hI => by
  rw [runT]; exact agreeI_pure rfl hI

theorem runFrameI_tt : TermFrame K ρ φ σ s₀ ks .tt := fun tl hint s s' hI => by
  rw [runT]; exact agreeI_pure rfl hI

/-- **An embedded value** (it reads no state): the same meaning and type on both sides, no label, the strict test
the same. -/
theorem runFrameI_val (v : Value) : TermFrame K ρ φ σ s₀ ks (.val v) := fun tl hint s s' hI => by
  rw [runT_val_def, runT_val_def]
  refine agreeI_of_vagree ?_
  have hl : (meanV K ρ φ hint v, ({ valT K ρ φ hint v with label := none } : TyS)).2.label = none := rfl
  generalize (meanV K ρ φ hint v, ({ valT K ρ φ hint v with label := none } : TyS)) = r at hl ⊢
  cases v with
  | ind ty c hd ps fs =>
    simp only [strictVal]
    split
    · trivial
    · unfold SM.strictS
      simp only [pure]
      split
      · exact ⟨⟨rfl, hl⟩, hI⟩
      · trivial
  | clo caps t rd =>
    simp only [strictVal]
    split
    · trivial
    · exact ⟨⟨rfl, hl⟩, hI⟩
  | sealed t =>
    simp only [strictVal]
    split
    · trivial
    · exact ⟨⟨rfl, hl⟩, hI⟩
  | _ => exact ⟨⟨rfl, hl⟩, hI⟩


end

/-! ## Combinators -/

section
variable {K : RunCtx} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- The strict test of a result's membership, on both sides or neither. -/
theorem agreeI_strictS {x x' : SM Res} {s s' : SState} (R : DataRead)
    (h : FrameAgreeI K φ σ s₀ ks (x s) (x' s')) : FrameAgreeI K φ σ s₀ ks (SM.strictS R x s) (SM.strictS R x' s') := by
  unfold SM.strictS
  match x s, x' s', h with
  | some (r, t), some (r', t'), hr =>
    have e : r = renRes σ r' := agree_renRes hr
    subst e
    dsimp only
    split
    · rw [if_pos (by simpa [renRes] using ‹_›)]; exact hr
    · rw [if_neg (by simpa [renRes] using ‹_›)]; trivial
  | none, none, _ => trivial

/-- A bind on two runs that agree in value, into agreeing runs. -/
theorem agreeI_vbind {α : Type 3} {E : α → α → Prop} {x x' : SM α} {f f' : α → SM Res} {s s' : SState}
    (h : VAgree K φ σ s₀ ks E (x s) (x' s'))
    (hf : ∀ a a' t t', E a a' → FrameInv K φ σ s₀ ks t t' → FrameAgreeI K φ σ s₀ ks (f a t) (f' a' t')) :
    FrameAgreeI K φ σ s₀ ks ((x >>= f) s) ((x' >>= f') s') := by
  show FrameAgreeI K φ σ s₀ ks (match x s with | some (a, t) => f a t | none => none)
    (match x' s' with | some (a, t) => f' a t | none => none)
  match x s, x' s', h with
  | some (a, t), some (a', t'), ⟨e, hI⟩ => exact hf a a' t t' e hI
  | none, none, _ => trivial

/-- A bind on two agreeing runs (SM level), the continuation at the closure's result renamed, with the result's label
parked and its records. -/
theorem agreeI_smbind {x x' : SM Res} {f f' : Res → SM Res} {s s' : SState}
    (h : FrameAgreeI K φ σ s₀ ks (x s) (x' s'))
    (hf : ∀ (r' : Res) (t t' : SState), FrameInv K φ σ s₀ ks t t' →
      ResAtTemp s₀ t (r'.2.label.map σ) ∧ ResDead t' r'.2.label →
      FrameAgreeI K φ σ s₀ ks (f (renRes σ r') t) (f' r' t')) :
    FrameAgreeI K φ σ s₀ ks ((x >>= f) s) ((x' >>= f') s') := by
  rw [sm_bind_eq, sm_bind_eq]
  match x s, x' s', h with
  | some (r, t), some (r', t'), hr =>
    have e : r = renRes σ r' := agree_renRes hr
    subst e
    exact hf r' t t' hr.2.2.1 hr.2.2.2
  | none, none, _ => trivial

end

/-! ## Successor, reference types, equalities, annotations -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

theorem runFrameI_succ {u : Term} (ihu : TermFrame K ρ φ σ s₀ ks u) : TermFrame K ρ φ σ s₀ ks (.succ u) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI (agreeI_strictS _ (agreeI_smbind (ihu false _ s s' hI) fun r' t t' ht _ => ?_))
  obtain ⟨v, R'⟩ := r'
  rcases Option.eq_none_or_eq_some R'.label with hl | ⟨l, hl⟩
  · simp only [renRes, hl, Option.map_none]
    exact agreeI_pure rfl ht
  · simp only [renRes, hl, Option.map_some]
    trivial

theorem runFrameI_ref {A : Term} (ihA : TermFrame K ρ φ σ s₀ ks A) : TermFrame K ρ φ σ s₀ ks (.ref A) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI (agreeI_strictS _ (agreeI_vbind (vagree_run ihA false _ hI) fun a a' t t' e ht => ?_))
  obtain ⟨TA, _⟩ := a
  obtain ⟨TA', _⟩ := a'
  obtain ⟨e1, -⟩ := e
  simp only at e1; subst e1
  exact agreeI_pure rfl ht

open Classical in
theorem runFrameI_eq {A a b : Term} (ihA : TermFrame K ρ φ σ s₀ ks A) (iha : TermFrame K ρ φ σ s₀ ks a)
    (ihb : TermFrame K ρ φ σ s₀ ks b) : TermFrame K ρ φ σ s₀ ks (.eq A a b) := by
  intro tl hint s s' hI
  rw [runT]
  refine agreeI_of_vagree (vagree_onCopy hI (vagree_bind (vagree_run ihA false _ hI) fun x x' t t' e ht => ?_))
  obtain ⟨TA, _⟩ := x; obtain ⟨TA', _⟩ := x'
  obtain ⟨e1, -⟩ := e; simp only at e1; subst e1
  refine vagree_bind (vagree_onCopy ht (vagree_run iha false _ ht)) fun y y' t2 t2' e2 ht2 => ?_
  obtain ⟨va, _⟩ := y; obtain ⟨va', _⟩ := y'
  obtain ⟨e3, -⟩ := e2; simp only at e3; subst e3
  refine vagree_bind (vagree_onCopy ht2 (vagree_run ihb false _ ht2)) fun z z' t3 t3' e4 ht3 => ?_
  obtain ⟨vb, _⟩ := z; obtain ⟨vb', _⟩ := z'
  obtain ⟨e5, -⟩ := e4; simp only at e5; subst e5
  exact vagree_test ht3 ⟨rfl, rfl⟩

/-- A proof built from premises run on copies (`cong`, `symm`, `trans`, `rewrite`, `rewriteR`). -/
theorem agreeI_premises {s s' : SState} (hI : FrameInv K φ σ s₀ ks s s') :
    ∀ (xs : List Term), (∀ a ∈ xs, TermFrame K ρ φ σ s₀ ks a) →
      VAgree K φ σ s₀ ks ResN
        ((xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k) (pure (.proof, .plain (TyM.prop True))))
          s)
        ((xs.foldr (fun t k => runT K ρ φ false (.plain TyM.err) t >>= fun _ => k) (pure (.proof, .plain (TyM.prop True))))
          s')
  | [], _ => vagree_pure hI ⟨rfl, rfl⟩
  | a :: xs, ih => by
    simp only [List.foldr_cons]
    exact vagree_bind (vagree_run (ih a (List.mem_cons_self ..)) false _ hI) fun _ _ t t' _ ht =>
      agreeI_premises ht xs (fun b hb => ih b (List.mem_cons_of_mem _ hb))

theorem runFrameI_cong {f h : Term} (ihh : TermFrame K ρ φ σ s₀ ks h) : TermFrame K ρ φ σ s₀ ks (.cong f h) := by
  intro tl hint s s' hI
  rw [runT]
  exact agreeI_of_vagree (vagree_onCopy hI (agreeI_premises hI [h] (by simpa using ihh)))

open Classical in
/-- **An annotation** (`u : A`): the annotation on a copy, the term at it, its label's content type tested on both sides
or neither (`labTyOk_corr`), the strict membership test (`agreeI_strictS`). -/
theorem runFrameI_ascribe {u A : Term} (ihu : TermFrame K ρ φ σ s₀ ks u) (ihA : TermFrame K ρ φ σ s₀ ks A) :
    TermFrame K ρ φ σ s₀ ks (.ascribe u A) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI (agreeI_strictS _ (agreeI_vbind (vagree_onCopy hI (vagree_run ihA false _ hI))
    fun x x' t t' e ht => ?_))
  obtain ⟨TA, _⟩ := x; obtain ⟨TA', _⟩ := x'
  obtain ⟨e1, -⟩ := e; simp only at e1; subst e1
  refine agreeI_smbind (ihu false _ t t' ht) fun r' w w' hw hres => ?_
  obtain ⟨v, R'⟩ := r'
  have hiff := labTyOk_corr hw (R := { R' with label := R'.label.map σ }) rfl hres.2 (TyS.plain TA.asTy).m
  show FrameAgreeI K φ σ s₀ ks
    (if labTyOk w (R'.label.map σ) (TyS.plain TA.asTy).m then
      some ((v, { (TyS.plain TA.asTy) with label := R'.label.map σ }), w) else none)
    (if labTyOk w' R'.label (TyS.plain TA.asTy).m then some ((v, { (TyS.plain TA.asTy) with label := R'.label }), w')
      else none)
  by_cases hk : labTyOk w' R'.label (TyS.plain TA.asTy).m
  · rw [if_pos (hiff.2 hk), if_pos hk]
    exact ⟨rfl, rfl, hw, hres⟩
  · rw [if_neg (fun h' => hk (hiff.1 h')), if_neg hk]; trivial


end

/-! ## Inductive types and constructors -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- An inductive's parameters (each a statement on a copy): the same meanings on both sides. -/
theorem runParams_vagree (d : IndDecl) :
    ∀ (args : List Term), (∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) → ∀ (i : Nat) (earlier : List Sem) {s s' : SState},
      FrameInv K φ σ s₀ ks s s' →
      VAgree K φ σ s₀ ks Eq (runParams K ρ φ d i earlier args s) (runParams K ρ φ d i earlier args s')
  | [], _, i, earlier, s, s', hI => by simp only [runParams]; exact vagree_pure hI rfl
  | a :: as, ih, i, earlier, s, s', hI => by
    simp only [runParams]
    refine vagree_bind (vagree_onCopy hI (vagree_run (ih a (List.mem_cons_self ..)) false _ hI))
      fun x x' t t' e ht => ?_
    obtain ⟨v, _⟩ := x; obtain ⟨v', _⟩ := x'
    obtain ⟨e1, -⟩ := e; simp only at e1; subst e1
    refine vagree_bind (runParams_vagree d as (fun b hb => ih b (List.mem_cons_of_mem _ hb)) _ _ ht)
      fun rest rest' t2 t2' e2 ht2 => ?_
    subst e2
    exact vagree_pure ht2 rfl

open Classical in
theorem runFrameI_tind {n : String} {args : List Term} (ih : ∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) :
    TermFrame K ρ φ σ s₀ ks (.tind n args) := by
  intro tl hint s s' hI
  rw [runT]
  cases hfind : List.find? (fun x => x.name == n) K.Γ with
  | none => simp only [hfind]; trivial
  | some d =>
    simp only [hfind]
    refine agreeI_of_vagree (vagree_bind (runParams_vagree d args ih 0 [] hI) fun psM psM' t t' e ht => ?_)
    subst e
    exact vagree_test ht ⟨rfl, rfl⟩

/-- A statement position keeps agreement in value. -/
theorem vagree_stmtIf (b : Bool) {x x' : SM Res} {s s' : SState} (hI : FrameInv K φ σ s₀ ks s s')
    (h : VAgree K φ σ s₀ ks ResV (x s) (x' s')) : VAgree K φ σ s₀ ks ResV (SM.stmtIf b x s) (SM.stmtIf b x' s') := by
  cases b with
  | false => exact h
  | true =>
    simp only [SM.stmtIf, if_true]
    match x s, x' s', h with
    | some (r, t), some (r', t'), ⟨e, _⟩ => exact ⟨e, hI⟩
    | none, none, _ => trivial

/-- Unifying a field's declared type with the type its run returned reads the type, not its label. -/
theorem unifyTyS_m (dm : DataModel) (np : Nat) (FT : Term) {R R' : TyS} (hm : R.m = R'.m) (sol : List (Option Sem)) :
    unifyTyS dm np FT R sol = unifyTyS dm np FT R' sol := by
  cases FT with
  | place p => cases p <;> simp [unifyTyS, hm]
  | tind m as => simp [unifyTyS, TyS.data, hm]
  | _ => simp [unifyTyS]

/-- A constructor's fields: the same meanings and solved parameters on both sides. -/
theorem runFields_vagree (stmt : Bool) (d : IndDecl) (c : Nat) (rh : Option Rec) :
    ∀ (args : List Term), (∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) → ∀ (i : Nat) (sol : List (Option Sem))
      (earlier : List Sem) {s s' : SState}, FrameInv K φ σ s₀ ks s s' →
      VAgree K φ σ s₀ ks Eq (runFields K ρ φ stmt d c i rh sol earlier args s)
        (runFields K ρ φ stmt d c i rh sol earlier args s')
  | [], _, i, sol, earlier, s, s', hI => by simp only [runFields]; exact vagree_pure hI rfl
  | a :: as, ih, i, sol, earlier, s, s', hI => by
    simp only [runFields]
    rw [scopeOf_corr hI.acc.rel]
    refine vagree_bind (vagree_stmtIf _ hI (vagree_run (ih a (List.mem_cons_self ..)) false _ hI))
      fun x x' t t' e ht => ?_
    obtain ⟨v, R⟩ := x; obtain ⟨v', R'⟩ := x'
    obtain ⟨e1, e2⟩ := e; simp only at e1 e2; subst e1
    dsimp only
    have hsol : ∀ FT, unifyTyS K.dm d.params.length FT R sol = unifyTyS K.dm d.params.length FT R' sol :=
      fun FT => unifyTyS_m _ _ FT e2 _
    simp only [hsol]
    refine vagree_bind (runFields_vagree stmt d c rh as (fun b hb => ih b (List.mem_cons_of_mem _ hb)) _ _ _ ht)
      fun y y' t2 t2' e3 ht2 => ?_
    subst e3
    obtain ⟨rest, sol₂⟩ := y
    exact vagree_pure ht2 rfl

open Classical in
/-- A constructor value's strict result, the same on both sides, with no label. -/
theorem ctor_strict_vagree {t t' : SState} (ht : FrameInv K φ σ s₀ ks t t') (d : IndDecl) (c : Nat) (fs : List Sem)
    (rr : Option Rec) :
    VAgree K φ σ s₀ ks ResN (SM.strictS K.dm.read (ctorOut K.dm d c fs rr) t)
      (SM.strictS K.dm.read (ctorOut K.dm d c fs rr) t') := by
  unfold SM.strictS
  cases rr with
  | none => trivial
  | some r =>
    simp only [ctorOut, pure]
    exact vagree_test ht ⟨rfl, rfl⟩

open Classical in
/-- **A constructor**: its parameters and fields agree in value (`runParams_vagree`, `runFields_vagree`), the record and
the strict test are the same on both sides, and the value built has no label. -/
theorem runFrameI_ctor {ty : String} {c : Nat} {x : Hint} {ps args : List Term}
    (ihps : ∀ a ∈ ps, TermFrame K ρ φ σ s₀ ks a) (ihargs : ∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) :
    TermFrame K ρ φ σ s₀ ks (.ctor ty c x ps args) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  cases hfind : List.find? (fun x => x.name == ty) K.Γ with
  | none => simp only [hfind]; trivial
  | some d =>
    simp only [hfind]
    refine agreeI_of_vagree (vagree_bind (runParams_vagree d ps ihps 0 [] hI) fun psM psM' t t' e ht => ?_)
    subst e
    refine vagree_bind (runFields_vagree _ d c _ args ihargs 0 _ [] ht) fun y y' t2 t2' e2 ht2 => ?_
    subst e2
    obtain ⟨fs, sol⟩ := y
    dsimp only
    split
    · exact ctor_strict_vagree ht2 _ _ _ _
    · trivial


end

/-! ## Primitives that fail -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {tl : Bool} {hint : TyS} {s : SState} {n : String}

theorem prim_none_nil : runT K ρ φ tl hint (.prim n []) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_one {u : Term} (h1 : n ≠ "symm") (h2 : n ≠ "clone") (h3 : n ≠ "peek") (h4 : n ≠ "inplace") :
    runT K ρ φ tl hint (.prim n [u]) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_two {a b : Term} (h1 : n ≠ "trans") (h2 : n ≠ "rewrite") (h3 : n ≠ "rewriteR")
    (h4 : ¬ (n = "split" ∧ ∃ f, a = .const f)) : runT K ρ φ tl hint (.prim n [a, b]) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_three {a b c : Term} : runT K ρ φ tl hint (.prim n [a, b, c]) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_four {a b c d : Term} : runT K ρ φ tl hint (.prim n [a, b, c, d]) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_five {a b c d e : Term} : runT K ρ φ tl hint (.prim n [a, b, c, d, e]) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_six {A a b P h t : Term} (hJ : n ≠ "J") : runT K ρ φ tl hint (.prim n [A, a, b, P, h, t]) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

theorem prim_none_many {a b c d e f g : Term} {rest : List Term} :
    runT K ρ φ tl hint (.prim n (a :: b :: c :: d :: e :: f :: g :: rest)) s = none := by
  rw [runT]
  · rfl
  all_goals (intros; simp_all)

end

/-! ## `J` -/

/-- A call's value and its type's code read the callee's meaning and the arguments' values only: the state changes
(takes, fixes, a returned borrow's fresh label and lending) do not reach them. -/
theorem callOfL_val.{u} (L : Lvl.{u}) {C : Type u} (t : Tel L.Code PUnit C) (fv : Sem) {args args' : List Res}
    (ha : args.map (·.1) = args'.map (·.1)) (s s' : SState) :
    (callOfL L t fv args s).map (fun x => (x.1.1, x.1.2.m)) = (callOfL L t fv args' s').map (fun x => (x.1.1, x.1.2.m)) := by
  unfold callOfL
  dsimp only
  rw [ha]
  cases applyFnL L t fv (args'.map (·.1)) with
  | none => rfl
  | some x => cases x <;> rfl

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {σ : Nat → Nat} {s₀ : SState} {ks : List Nat}

/-- A call on a copy (`J`'s motive at the first endpoint): the same value and type on both sides. -/
theorem callOf_vagree {s s' : SState} (hI : FrameInv K φ σ s₀ ks s s') {fv fv' : Res} (hf : ResV fv fv')
    (args args' : List Res) (ha : args.map (·.1) = args'.map (·.1)) :
    VAgree K φ σ s₀ ks ResV (SM.onCopy (callOf K.dm.read fv args) s) (SM.onCopy (callOf K.dm.read fv' args') s') := by
  obtain ⟨v, T⟩ := fv; obtain ⟨v', T'⟩ := fv'
  obtain ⟨e1, e2⟩ := hf; simp only at e1 e2; subst e1
  have key : ∀ (o o' : Option (Res × SState)), o.map (fun x => (x.1.1, x.1.2.m)) = o'.map (fun x => (x.1.1, x.1.2.m)) →
      VAgree K φ σ s₀ ks ResV (o.map fun (a, _) => (a, s)) (o'.map fun (a, _) => (a, s')) := by
    intro o o' e
    match o, o', e with
    | none, none, _ => trivial
    | some (r, _), some (r', _), e =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      exact ⟨⟨e.1, e.2⟩, hI⟩
  unfold SM.onCopy callOf
  dsimp only
  rw [e2]
  split
  · exact key _ _ (callOfL_val _ _ _ ha s s')
  · exact key _ _ (callOfL_val _ _ _ ha s s')
  · exact key _ _ (callOfL_val _ _ _ ha s s')
  · trivial

/-- **The frame property's clause for `J`** (the paper's row "A match", with one arm: `J` computes): its endpoints,
motive and proof as statements on copies (`VAgree`), the motive at the first endpoint on a copy (`callOf_vagree`), then
[Entry] (`entry_frameInv`), the transported term (the induction), the join's drop (`joinDrop_corr`). -/
theorem runFrameI_J (hs₀ : FrameStart s₀ ks) {A a b P h t : Term} (ihA : TermFrame K ρ φ σ s₀ ks A)
    (iha : TermFrame K ρ φ σ s₀ ks a) (ihb : TermFrame K ρ φ σ s₀ ks b) (ihP : TermFrame K ρ φ σ s₀ ks P)
    (ihh : TermFrame K ρ φ σ s₀ ks h) (iht : TermFrame K ρ φ σ s₀ ks t) :
    TermFrame K ρ φ σ s₀ ks (.prim "J" [A, a, b, P, h, t]) := by
  intro tl hint s s' hI
  rw [runT]; dsimp only
  rw [scopeOf_corr hI.acc.rel]
  refine agreeI_erasedIf _ hI ?_
  refine agreeI_vbind (vagree_onCopy hI (vagree_run ihA false _ hI)) fun _ _ t1 t1' _ h1 => ?_
  refine agreeI_vbind (vagree_onCopy h1 (vagree_run iha false _ h1)) fun ra ra' t2 t2' e2 h2 => ?_
  refine agreeI_vbind (vagree_onCopy h2 (vagree_run ihb false _ h2)) fun _ _ t3 t3' _ h3 => ?_
  refine agreeI_vbind (vagree_onCopy h3 (vagree_run ihP false _ h3)) fun rP rP' t4 t4' e4 h4 => ?_
  refine agreeI_vbind (vagree_onCopy h4 (vagree_run ihh false _ h4)) fun _ _ t5 t5' _ h5 => ?_
  refine agreeI_vbind (callOf_vagree h5 e4 [ra] [ra'] (by simp [e2.1])) fun rPa rPa' t6 t6' e6 h6 => ?_
  obtain ⟨e61, -⟩ := e6
  rw [e61]
  obtain ⟨hmeI, hmeF⟩ := entry_frameInv hs₀ h6 true t
  by_cases hme : MatchEntryOk K φ true t t6
  rotate_left
  · rw [if_neg hme, if_neg (fun h' => hme (hmeI.2 h'))]; trivial
  rw [if_pos hme, if_pos (hmeI.1 hme)]
  have hE := hmeF hme
  rw [movedPlaces_corr φ hE.acc.rel hE.acc.shape hE.acc.loc]
  have hrun := iht false (.plain rPa'.1.asTy) _ _ hE
  generalize movedPlaces φ (matchEntry K φ true t t6').1 = entry
  cases e7 : runT K ρ φ false (.plain rPa'.1.asTy) t (matchEntry K φ true t t6).1 with
  | none =>
    rw [e7] at hrun
    cases e8 : runT K ρ φ false (.plain rPa'.1.asTy) t (matchEntry K φ true t t6').1 with
    | none => trivial
    | some _ => rw [e8] at hrun; exact hrun.elim
  | some y =>
    rw [e7] at hrun
    cases e8 : runT K ρ φ false (.plain rPa'.1.asTy) t (matchEntry K φ true t t6').1 with
    | none => rw [e8] at hrun; exact hrun.elim
    | some y' =>
      rw [e8] at hrun
      obtain ⟨⟨r, R⟩, u⟩ := y
      obtain ⟨⟨r', R'⟩, u'⟩ := y'
      obtain ⟨er, hR, hu, hres⟩ := hrun
      simp only at er; subst er
      dsimp only
      obtain ⟨hjacc, hjok⟩ := joinDrop_corr (φ := φ) hs₀ entry (.prim "J" [A, a, b, P, h, t]) hu.acc
      by_cases hj : JoinDropOk K φ entry (.prim "J" [A, a, b, P, h, t]) u
      · rw [if_pos hj, if_pos (hjok.1 hj)]
        have hsh := shrinks_joinDrop K φ entry (.prim "J" [A, a, b, P, h, t]) u
        have hsh' := shrinks_joinDrop K φ entry (.prim "J" [A, a, b, P, h, t]) u'
        refine ⟨rfl, hR, hu.of_ops hjacc (Strict.sgood_joinDrop hu.good entry _ hj)
          (Strict.sgood_joinDrop hu.good' entry _ (hjok.1 hj)) hsh hsh', hres.1.shrinks hu.acc.uniq hsh,
          hres.2.shrinks hsh'⟩
      · rw [if_neg hj, if_neg (fun h' => hj (hjok.2 h'))]; trivial


/-- A primitive's run where no pattern of `runT` applies: a failure on both sides. -/
theorem runFrameI_prim_fail {n : String} {args : List Term}
    (hf : ∀ tl hint (s : SState), runT K ρ φ tl hint (.prim n args) s = none) : TermFrame K ρ φ σ s₀ ks (.prim n args) :=
  fun tl hint s s' _ => by rw [hf, hf]; trivial

/-- **The frame property's clause for a primitive**: proofs from premises on copies (`symm`, `trans`, `rewrite`,
`rewriteR`), a read in place of a stuck block's capture (`clone`, `peek`, `inplace`: a copying read, or the term),
`split f in u` (its term), `J` (`runFrameI_J`); any other form fails on both sides. -/
theorem runFrameI_prim (hs₀ : FrameStart s₀ ks) {n : String} {args : List Term}
    (ih : ∀ a ∈ args, TermFrame K ρ φ σ s₀ ks a) : TermFrame K ρ φ σ s₀ ks (.prim n args) := by
  match args, ih with
  | [], _ => exact runFrameI_prim_fail fun _ _ _ => prim_none_nil
  | [u], ih =>
    have ihu := ih u (List.mem_singleton_self _)
    by_cases hc : n = "clone" ∨ n = "peek" ∨ n = "inplace"
    · intro tl hint s s' hI
      rcases hc with rfl | rfl | rfl <;>
      · rw [runT]; dsimp only
        rw [scopeOf_corr hI.acc.rel]
        refine agreeI_erasedIf _ hI ?_
        cases u <;> first | exact readCopy_agree hs₀ hI _ | exact ihu false hint s s' hI
    by_cases e1 : n = "symm"
    · subst e1
      intro tl hint s s' hI
      rw [runT]
      exact agreeI_of_vagree (vagree_onCopy hI (agreeI_premises hI [u] ih))
    exact runFrameI_prim_fail fun _ _ _ => prim_none_one e1 (fun e => hc (.inl e)) (fun e => hc (.inr (.inl e)))
      (fun e => hc (.inr (.inr e)))
  | [a, b], ih =>
    by_cases e2 : n = "trans" ∨ n = "rewrite" ∨ n = "rewriteR"
    · intro tl hint s s' hI
      rcases e2 with rfl | rfl | rfl <;>
      · rw [runT]
        exact agreeI_of_vagree (vagree_onCopy hI (agreeI_premises hI [a, b] ih))
    by_cases hsp : n = "split" ∧ ∃ f, a = .const f
    · obtain ⟨rfl, f, rfl⟩ := hsp
      have ihb := ih b (by simp)
      intro tl hint s s' hI
      rw [runT]; dsimp only
      rw [scopeOf_corr hI.acc.rel]
      exact agreeI_erasedIf _ hI (ihb tl hint s s' hI)
    exact runFrameI_prim_fail fun _ _ _ => prim_none_two (fun e => e2 (.inl e)) (fun e => e2 (.inr (.inl e)))
      (fun e => e2 (.inr (.inr e))) hsp
  | [a, b, c], _ => exact runFrameI_prim_fail fun _ _ _ => prim_none_three
  | [a, b, c, d], _ => exact runFrameI_prim_fail fun _ _ _ => prim_none_four
  | [a, b, c, d, e], _ => exact runFrameI_prim_fail fun _ _ _ => prim_none_five
  | [A, a, b, P, h, t], ih =>
    by_cases hJ : n = "J"
    · subst hJ
      exact runFrameI_J hs₀ (ih A (by simp)) (ih a (by simp)) (ih b (by simp)) (ih P (by simp)) (ih h (by simp))
        (ih t (by simp))
    exact runFrameI_prim_fail fun _ _ _ => prim_none_six hJ
  | a :: b :: c :: d :: e :: f :: g :: rest, _ => exact runFrameI_prim_fail fun _ _ _ => prim_none_many

end

end Ochr.Meaning.Steps.Form.FrameEnd
