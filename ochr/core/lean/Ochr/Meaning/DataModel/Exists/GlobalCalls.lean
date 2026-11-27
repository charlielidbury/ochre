import Ochr.Meaning.DataModel.Exists.FieldLevel
import Ochr.Meaning.Steps.Machine.CheckItem

/-!
# A global whose stored codomain is `Prop` or `Type` calls to level-0 type values (exists12)

`Assembly.GlobalCallLevels`, the one fact about the model among the eight `exists_dataModel`
assumed (docs/34 §18.16), PROVED here, with no hypothesis, at every stage of every program
(`callsLevel0_stage`). Three steps, as docs/18's `<sec-n1-facts>` planned them, the third restated
as the sixth referee's objection Y3 asked:
1. **The stage invariant** (`TyInv`, `tyInv_progMeaningFrom`): the stage's type of a global is `err`,
   or the meaning (`globalTyS`) of a stored type value that is `.bot` or the stored type of the FIRST
   global of that name in the stage's globals. The globals only grow at the end
   (`Steps.Machine.checkItem_tables`), so the first entry stays first.
2. **A written Π-type with a sort codomain** (`globalTyS_tPi_sort`): its meaning is `err` or
   `piTyAt R l' ps out` with `out` not a borrow and its codomain constantly `univ l`.
3. **The terminal code of the telescope** (`DatLeaf`, `telL_datLeaf`, `callOfL_datLeaf`): a call
   along a telescope all of whose leaves are the data code `c₀` gives an encoding at `c₀` itself, not
   merely at some code of the level (the referee's point: `LeafOk.callOfL_enc` gives only the latter,
   which at level 2 includes `Code2.univ2`, whose encodings are level-1 type values). For `univ 0` and
   `univ 1` the level-2 code is a lift, `Code2.enc (.lift _ c) a = Code1.enc c a.down`, a level-0 type
   value (`FieldLevel.enc1_lvl0`).
-/

namespace Ochr.Meaning.DataModel.Exists.GlobalCalls

open Ochr Ochr.Meaning

universe u

/-! ## Step 3: the terminal code of a telescope -/

/-- **Every leaf of a telescope code is the data code `p`** (no returned borrow): what a call along it
returns is an encoding at `p`. -/
inductive DatLeaf {Code : Type u → Type (u + 1)} (p : (B : Type u) × Code B) :
    {Fin C : Type u} → Tel Code Fin C → Prop
  | dat (Fin : Type u) : DatLeaf p (Tel.dat Fin p.1 p.2)
  | param (Fin : Type u) (isRef : Bool) (A : Type u) (c : Code A) (C : A → Type u)
      (k : (a : A) → Tel Code (extFin isRef Fin A) (C a)) :
      (∀ a, DatLeaf p (k a)) → DatLeaf p (Tel.param Fin isRef A c C k)

/-- **`telL` at a constant borrow-free codomain**: every leaf is the codomain's code. -/
theorem telL_datLeaf (L : Lvl.{u}) (T0 : TyM) :
    ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (out : PiCod), out.isRef = false →
      (∀ acc, out.cod acc = T0) → DatLeaf (L.codeOf T0) (telL L ds acc Fin out).2
  | [], acc, Fin, ⟨isRef, cod⟩, hr, hc => by
    simp only at hr
    subst hr
    have e : cod acc = T0 := hc acc
    show DatLeaf (L.codeOf T0) (Tel.dat Fin (L.codeOf (cod acc)).1 (L.codeOf (cod acc)).2)
    rw [e]
    exact DatLeaf.dat Fin
  | p :: ps, acc, Fin, out, hr, hc => by
    show DatLeaf (L.codeOf T0) (Tel.param Fin p.isRef _ (L.codeOf (p.dom acc)).2 _ fun a =>
      (telL L ps (acc ++ [L.enc (L.codeOf (p.dom acc)).2 a]) (extFin p.isRef Fin (L.codeOf (p.dom acc)).1) out).2)
    exact DatLeaf.param _ _ _ _ _ _ fun a => telL_datLeaf L T0 ps _ _ out hr hc

/-- **A call along such a telescope returns an encoding at its leaf code.** -/
theorem applyTelL_datLeaf (L : Lvl.{u}) (p : (B : Type u) × L.Code B) :
    ∀ {Fin C : Type u} (t : Tel L.Code Fin C), DatLeaf p t →
      ∀ (readFin : Fin → List Sem) (F : C) (args : List Sem) (res : AppResultL L),
        applyTelL L t readFin F args = some res → ∃ (x : p.1) (T : TyM) (fins : List Sem), res = .data (L.enc p.2 x) T fins
  | _, _, _, .dat Fin, readFin, F, [], res, h => by
    simp only [applyTelL, Option.some.injEq] at h
    exact ⟨F.1, _, _, h.symm⟩
  | _, _, _, .dat Fin, readFin, F, _ :: _, res, h => by simp [applyTelL] at h
  | _, _, _, .param Fin isRef A c C k hk, readFin, F, [], res, h => by simp [applyTelL] at h
  | _, _, _, .param Fin isRef A c C k hk, readFin, F, a :: as, res, h => by
    simp only [applyTelL] at h
    cases hx : L.dec c a with
    | none => rw [hx] at h; cases h
    | some x => rw [hx] at h; exact applyTelL_datLeaf L p (k x) (hk x) _ (F x) as res h

/-- **A call at level `L` along such a telescope gives an encoding at the leaf code** (`Run.callOfL`:
the borrow-returning branch needs a `.ref` leaf, which there is none of). -/
theorem callOfL_datLeaf (L : Lvl.{u}) (p : (B : Type u) × L.Code B) {C : Type u} (t : Tel L.Code PUnit C)
    (ht : DatLeaf p t) (fv : Sem) (args : List Res) (s : SState) {r : Res} {s' : SState}
    (h : callOfL L t fv args s = some (r, s')) : ∃ x : p.1, r.1 = L.enc p.2 x := by
  unfold callOfL at h
  dsimp only at h
  split at h
  · rename_i r0 T finals happ
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    unfold applyFnL at happ
    obtain ⟨F, -, hF⟩ := Option.bind_eq_some_iff.1 happ
    obtain ⟨x, _, _, e⟩ := applyTelL_datLeaf L p t ht _ F _ _ hF
    cases e
    exact ⟨x, rfl⟩
  · rename_i U c fwd back happ
    unfold applyFnL at happ
    obtain ⟨F, -, hF⟩ := Option.bind_eq_some_iff.1 happ
    obtain ⟨x, _, _, e⟩ := applyTelL_datLeaf L p t ht _ F _ _ hF
    cases e
  · cases h

/-! ## Step 2: a written Π-type with a sort codomain -/

/-- **The run of a written Π-term whose codomain is a sort** (`runT`'s `.pi` clause): a type value
`piTyAt R l' ps out`, `out` borrow-free with codomain constantly `univ l`. -/
theorem runT_pi_sort (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (h : TyS) (hs : List Hint)
    (ds : List Term) (l : Nat) (s : SState) {r : Res} {s' : SState}
    (hr : runT K ρ φ tl h (.pi hs ds (.sort l)) s = some (r, s')) :
    ∃ (R : DataRead) (l' : Nat) (ps : List PiDom) (out : PiCod), out.isRef = false ∧
      (∀ acc, out.cod acc = TyM.univ l) ∧ r.1 = .ty (piTyAt R l' ps out) := by
  rw [runT] at hr
  dsimp only at hr
  split at hr
  · cases hr
    refine ⟨_, _, _, _, rfl, fun acc => ?_, rfl⟩
    dsimp only
    rw [RunLemmas.runT_sort]
    rfl
  · cases hr

open Classical in
/-- **The meaning of a stored type `Π(x̄ : Ā). sort l`** (`globalTyS`): `err`, or `piTyAt R l' ps out`
with `out` borrow-free and constantly `univ l`. -/
theorem globalTyS_tPi_sort (ρ : Assignment) (K : RunCtx) (cs : List Value) (hs : List Hint) (ds : List Term)
    (l : Nat) (rd : List (DeclInfo × Value)) :
    (globalTyS ρ K (.tPi cs (.pi hs ds (.sort l)) rd)).m = TyM.err ∨
      ∃ (R : DataRead) (l' : Nat) (ps : List PiDom) (out : PiCod), out.isRef = false ∧
        (∀ acc, out.cod acc = TyM.univ l) ∧ (globalTyS ρ K (.tPi cs (.pi hs ds (.sort l)) rd)).m = piTyAt R l' ps out := by
  unfold globalTyS Value.tyS
  rw [meanV_eq_mean]
  have key : ∀ X : TyM, X = (if CapsOk K.dm.read (capsVals K ρ noFuture cs) (capsTys K ρ noFuture rd) then
        match run K ρ noFuture (.plain TyM.err) (.pi hs ds (.sort l))
          (stateOf 0 (capsState (capsVals K ρ noFuture cs) (capsTys K ρ noFuture rd))) with
        | some ((v, _), _) => Sem.ty v.asTy
        | none => .ty TyM.err
      else .ty TyM.err).asTy → (X = TyM.err ∨ ∃ (R : DataRead) (l' : Nat) (ps : List PiDom) (out : PiCod),
        out.isRef = false ∧ (∀ acc, out.cod acc = TyM.univ l) ∧ X = piTyAt R l' ps out) := by
    intro X hX
    subst hX
    split
    · cases e : run K ρ noFuture (.plain TyM.err) (.pi hs ds (.sort l))
          (stateOf 0 (capsState (capsVals K ρ noFuture cs) (capsTys K ρ noFuture rd))) with
      | none => exact .inl rfl
      | some p =>
        obtain ⟨⟨v, T⟩, s'⟩ := p
        obtain ⟨R, l', ps, out, h1, h2, h3⟩ := runT_pi_sort K ρ noFuture false _ hs ds l _ e
        simp only at h3
        subst h3
        exact .inr ⟨R, l', ps, out, h1, h2, rfl⟩
    · exact .inl rfl
  exact key _ rfl

/-- The meaning of the stored type `.bot` (a definition whose stored type was not found) is `err`. -/
theorem globalTyS_bot (ρ : Assignment) (K : RunCtx) : (globalTyS ρ K .bot).m = TyM.err := by
  unfold globalTyS Value.tyS
  rw [meanV_eq_mean]
  rfl

/-! ## Calls through such a type -/

/-- A type that is not a level-2 code. -/
theorem not_t2_err : ∀ (B : Type 2) (c : Code2 B), TyM.err ≠ .t2 B c := fun _ _ h => by cases h

/-- **A function at a type `piTyAt R l' ps out`, `out` borrow-free and constantly `Prop` or `Type`,
calls to level-0 type values** at every model's read. At `l' ≤ 2` and above `3` the type is not a
level-2 code (`FieldLevel.callsLevel0_of_not_t2`); at `l' = 3` (a domain in `Type₁`) the call is an
encoding at the telescope's leaf code, `code2 (univ l)`, a lifted level-1 code (`callOfL_datLeaf`). -/
theorem callsLevel0_piTyAt (dmR : DataModel) (v : Sem) (T : TyS) (R : DataRead) (l' : Nat) (ps : List PiDom)
    (out : PiCod) (l : Nat) (hl : l ≤ 1) (hT : T.m = piTyAt R l' ps out) (hr : out.isRef = false)
    (hc : ∀ acc, out.cod acc = TyM.univ l) : FieldLevel.CallsLevel0 dmR (v, T) := by
  by_cases h3 : l' = 3
  · subst h3
    intro args s r s' hcall
    have hT' : T.m = .t2 _ (.pi _ (telL (lvl2 R) ps [] PUnit out).2) := hT
    unfold callOf at hcall
    simp only [hT'] at hcall
    have hleaf := telL_datLeaf (lvl2 R) (TyM.univ l) ps [] PUnit out hr hc
    obtain ⟨x, hx⟩ := callOfL_datLeaf (lvl2 dmR.read) (TyM.code2 (TyM.univ l)) (telL (lvl2 R) ps [] PUnit out).2
      hleaf v args s hcall
    rw [hx]
    rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · exact FieldLevel.enc1_lvl0 dmR Code1.univ0 x.down
    · exact FieldLevel.enc1_lvl0 dmR Code1.univ1 x.down
  · apply FieldLevel.callsLevel0_of_not_t2 dmR
    intro B c h
    change T.m = _ at h
    rw [hT] at h
    rcases l' with _ | _ | _ | _ | n
    · cases h
    · cases h
    · cases h
    · exact h3 rfl
    · cases h

/-! ## Step 1: the stage invariant -/

/-- **A stage's type of each global** is `err`, or the meaning (`globalTyS`) of a stored type value
that is `.bot` or the stored type of the first global of that name in the stage's globals. -/
def TyInv (ρ : Assignment) (P : ProgState) : Prop :=
  ∀ f, P.globalTy f = .plain TyM.err ∨
    ∃ (K : RunCtx) (V : Value), P.globalTy f = globalTyS ρ K V ∧
      (V = .bot ∨ (P.globals.find? (·.name == f)).map (·.ty) = some V)

theorem tyInv_empty (ρ : Assignment) : TyInv ρ {} := fun _ => .inl rfl

/-- A definition's meaning carries the meaning of its stored type. -/
theorem defMeaning_ty (ρ : Assignment) (K : RunCtx) (d : Def) (T : Value) :
    ((defMeaning ρ K d T).getD (.err, .plain .err)).2 = .plain .err ∨
      ((defMeaning ρ K d T).getD (.err, .plain .err)).2 = globalTyS ρ K T := by
  unfold defMeaning
  dsimp only
  split
  · cases run K ρ noFuture _ d.body (emptyState 0) <;> simp
  · cases run K ρ noFuture (.plain .err) _ (emptyState 0) <;> simp

theorem find?_prefix_map {gs gs' : List GDef} (hp : gs <+: gs') (f : String) {V : Value}
    (h : (gs.find? (·.name == f)).map (·.ty) = some V) : (gs'.find? (·.name == f)).map (·.ty) = some V := by
  obtain ⟨xs, rfl⟩ := hp
  rw [List.find?_append]
  cases e : gs.find? (·.name == f) with
  | none => rw [e] at h; cases h
  | some g => rw [e] at h; simpa using h

/-- **The invariant is kept by an item** (`Steps.Machine.checkItem_tables`: the globals grow at the
end; a definition's meaning is appended with the meaning of its stored type at the accepting state). -/
theorem tyInv_step (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (ρ : Assignment) (cfg : Config)
    (fuel : Nat) (P : ProgState) (it : Item) (h : TyInv ρ P) :
    TyInv ρ (ProgState.step dm D Γ ρ cfg fuel P it) := by
  unfold ProgState.step
  dsimp only
  split
  · rename_i st' hst
    obtain ⟨hI, hD⟩ := Steps.Machine.checkItem_tables it _ st' fuel hst
    cases it with
    | ind d =>
      have hg : st'.globals = P.globals := (hI d rfl).2
      intro f
      rcases h f with h | ⟨K, V, h1, h2⟩
      · exact .inl h
      · refine .inr ⟨K, V, h1, ?_⟩
        show V = .bot ∨ (st'.globals.find? (·.name == f)).map (·.ty) = some V
        rw [hg]; exact h2
    | defn d =>
      obtain ⟨-, g, hg⟩ := hD d rfl
      have hpre : P.globals <+: st'.globals := by rw [hg]; exact List.prefix_append _ _
      intro f
      show ProgState.globalTy { globals := st'.globals, inds := st'.inds, means := P.means ++ _ } f = _ ∨ _
      unfold ProgState.globalTy
      rw [List.find?_append]
      cases e : P.means.find? (·.1 == f) with
      | some x =>
        have hx : P.globalTy f = x.2.2 := by unfold ProgState.globalTy; rw [e]
        simp only [Option.some_or]
        rcases h f with h | ⟨K, V, h1, h2⟩
        · exact .inl (hx.symm.trans h)
        · refine .inr ⟨K, V, hx.symm.trans h1, ?_⟩
          rcases h2 with h2 | h2
          · exact .inl h2
          · exact .inr (find?_prefix_map hpre f h2)
      | none =>
        simp only [Option.none_or, List.find?_singleton]
        by_cases hn : d.name = f
        · subst hn
          simp only [beq_self_eq_true, ite_true]
          rcases defMeaning_ty ρ (P.ctx dm D Γ st') d (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot)
            with h1 | h1
          · exact .inl h1
          · refine .inr ⟨_, _, h1, ?_⟩
            cases e' : (st'.globals.find? (·.name == d.name)).map (·.ty) with
            | none => exact .inl rfl
            | some V => exact .inr rfl
        · have : (d.name == f) = false := by simpa using hn
          simp only [this]
          exact .inl rfl
  · exact h

/-- **Every stage keeps the invariant.** -/
theorem tyInv_progMeaningFrom (dm : DataModel) (D : MState → Decisions) (Γ : List IndDecl) (ρ : Assignment)
    (cfg : Config) (fuel : Nat) : ∀ (items : List Item) (P : ProgState), TyInv ρ P →
      TyInv ρ (progMeaningFrom dm D Γ ρ cfg fuel P items)
  | [], _, h => h
  | it :: items, P, h => by
    unfold progMeaningFrom
    rw [List.foldl_cons]
    exact tyInv_progMeaningFrom dm D Γ ρ cfg fuel items _ (tyInv_step dm D Γ ρ cfg fuel P it h)

/-! ## The fact -/

/-- **`GlobalCallLevels` at a stage** (PROVED, no hypothesis beyond the invariant): a global whose
first stored type in the stage is `Π(x̄ : Ā). sort l` with `l ≤ 1` calls, through the stage's meaning
of it, to level-0 type values or none, at every model's read. -/
theorem callsLevel0_of_tyInv (ρ : Assignment) (P : ProgState) (hP : TyInv ρ P) (f : String) (cs : List Value)
    (hs : List Hint) (ds : List Term) (l : Nat) (rd : List (DeclInfo × Value)) (hl : l ≤ 1)
    (hf : (P.globals.find? (·.name == f)).map (·.ty) = some (.tPi cs (.pi hs ds (.sort l)) rd)) (dmR : DataModel) :
    FieldLevel.CallsLevel0 dmR (P.baseC.global f) := by
  have herr : ∀ T : TyS, T.m = TyM.err → FieldLevel.CallsLevel0 dmR (P.globalMean f, T) := fun T hT =>
    FieldLevel.callsLevel0_of_not_t2 dmR _ fun B c h => by
      change T.m = _ at h; rw [hT] at h; cases h
  show FieldLevel.CallsLevel0 dmR (P.globalMean f, P.globalTy f)
  rcases hP f with h | ⟨K, V, h1, h2⟩
  · exact herr _ (by rw [h]; rfl)
  · rw [h1]
    rcases h2 with rfl | h2
    · exact herr _ (globalTyS_bot ρ K)
    · rw [hf] at h2
      cases h2
      rcases globalTyS_tPi_sort ρ K cs hs ds l rd with h | ⟨R, l', ps, out, hr, hc, hT⟩
      · exact herr _ h
      · exact callsLevel0_piTyAt dmR _ _ R l' ps out l hl hT hr hc

end Ochr.Meaning.DataModel.Exists.GlobalCalls
