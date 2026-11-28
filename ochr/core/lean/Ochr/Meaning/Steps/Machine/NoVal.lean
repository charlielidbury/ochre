import Ochr.Meaning.DataModel.Exists.Assembly

/-!
# `NoValFact`: resolution builds no embedded value (machine12's tool, finished by exists12)

`RRet P x`: every value a successful run of the resolver's computation `x` returns satisfies `P` (the resolver's
monad `R`, `Surface.lean`; the analogue of `RetP` for the checker's `M`). With it: no clause of `resolveF`
or `bindersF` builds a `Term.val` (`noVal_resolveF`, by induction on the fuel), so no item `resolveDecl`
returns holds one in a field or parameter type (`noVal_resolveDecl`, `noVal_runResolve`): the fact
`Assembly.NoValFact`, for the items a program resolves to (`Consistency.noValFact_of_resolvesTo`).
PROVED, standard axioms. (The checker itself accepts core declarations holding one, `FactsCE.EV`.)
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Surface

/-- A run of the resolver's monad, from the tables and a state. -/
def RRun {α : Type} (x : R α) (tb : Tables) (s : RState) : Except Exhausted (Except String α) × RState :=
  (((x.run tb).run).run).run s

/-- Every value a successful run of `x` returns satisfies `P`. -/
@[irreducible] def RRet {α : Type} (P : α → Prop) (x : R α) : Prop :=
  ∀ tb s a s', RRun x tb s = (.ok (.ok a), s') → P a

theorem RRun_pure {α : Type} (a : α) (tb : Tables) (s : RState) : RRun (pure a : R α) tb s = (.ok (.ok a), s) := rfl

theorem RRun_bind {α β : Type} (x : R α) (f : α → R β) (tb : Tables) (s : RState) :
    RRun (x >>= f) tb s = match RRun x tb s with
      | (.ok (.ok a), s₁) => RRun (f a) tb s₁
      | (.ok (.error e), s₁) => (.ok (.error e), s₁)
      | (.error e, s₁) => (.error e, s₁) := by
  unfold RRun
  simp only [ReaderT.run_bind, ExceptT.run_bind, StateT.run_bind]
  rcases ((ReaderT.run x tb).run.run).run s with ⟨r, s₁⟩
  rcases r with e | e | a <;> rfl


theorem RRet.pure' {α : Type} {P : α → Prop} {a : α} (h : P a) : RRet P (pure a : R α) := by
  unfold RRet; intro tb s a' s' hr
  rw [RRun_pure] at hr
  cases hr
  exact h

theorem RRet.bind_of {α β : Type} {Q : α → Prop} {P : β → Prop} {x : R α} {f : α → R β} (hx : RRet Q x)
    (h : ∀ a, Q a → RRet P (f a)) : RRet P (x >>= f) := by
  unfold RRet at *; intro tb s b s' hr
  rw [RRun_bind] at hr
  rcases e : RRun x tb s with ⟨r, s₁⟩
  rw [e] at hr
  rcases r with e' | e' | a
  · cases hr
  · cases hr
  · exact h a (hx tb s a s₁ e) tb s₁ b s' hr

theorem RRet.bind' {α β : Type} {P : β → Prop} {x : R α} {f : α → R β} (h : ∀ a, RRet P (f a)) :
    RRet P (x >>= f) :=
  RRet.bind_of (Q := fun _ => True) (by unfold RRet; exact fun _ _ _ _ _ => trivial) (fun a _ => h a)

theorem RRet.map_of {α β : Type} {Q : α → Prop} {P : β → Prop} {x : R α} {f : α → β} (hx : RRet Q x)
    (h : ∀ a, Q a → P (f a)) : RRet P (f <$> x) := by
  rw [← bind_pure_comp]
  exact RRet.bind_of hx fun a ha => RRet.pure' (h a ha)

theorem RRet.mono {α : Type} {P Q : α → Prop} {x : R α} (h : RRet P x) (hPQ : ∀ a, P a → Q a) : RRet Q x := by
  unfold RRet at *; exact fun tb s a s' hr => hPQ a (h tb s a s' hr)

theorem RRet.throw' {α : Type} {P : α → Prop} {e : String} : RRet P (throw e : R α) := by
  unfold RRet; intro tb s a s' hr
  cases hr

theorem RRet.exhausted' {α : Type} {P : α → Prop} {m : String} : RRet P (R.exhausted m : R α) := by
  unfold RRet; intro tb s a s' hr
  cases hr

theorem RRet.read' {P : Tables → Prop} (h : ∀ tb, P tb) : RRet P (read : R Tables) := by
  unfold RRet; intro tb s a s' hr
  cases hr
  exact h _

theorem RRet.modify' {f : RState → RState} : RRet (fun _ => True) (modify f : R Unit) := by
  unfold RRet; exact fun _ _ _ _ _ => trivial

theorem RRun_tryCatch {α : Type} (x : R α) (h : String → R α) (tb : Tables) (s : RState) :
    RRun (tryCatchThe String x h) tb s = match RRun x tb s with
      | (.ok (.ok a), s₁) => (.ok (.ok a), s₁)
      | (.ok (.error e), s₁) => RRun (h e) tb s₁
      | (.error e, s₁) => (.error e, s₁) := by
  unfold RRun
  show StateT.run (ExceptT.run (ExceptT.run (@ExceptT.tryCatch String (ExceptT Exhausted (StateM RState)) _ α
    (ReaderT.run x tb) fun e => ReaderT.run (h e) tb))) s = _
  simp only [ExceptT.tryCatch, StateT.run, ExceptT.run, ReaderT.run]
  rcases hx : x tb s with ⟨r, s₁⟩
  rcases r with e | e | a <;>
    simp [ExceptT.mk, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind, hx, pure, ExceptT.pure, StateT.pure]

theorem RRet.onFail' {α : Type} {P : α → Prop} {x : R α} {c : R Unit} (h : RRet P x) : RRet P (onFail x c) := by
  unfold RRet at *; intro tb s a s' hr
  unfold onFail at hr
  change RRun (tryCatchThe String x _) tb s = _ at hr
  rw [RRun_tryCatch] at hr
  rcases e : RRun x tb s with ⟨r, s₁⟩
  rw [e] at hr
  rcases r with e' | e' | a'
  · cases hr
  · dsimp only at hr
    rw [RRun_bind] at hr
    rcases e2 : RRun c tb s₁ with ⟨r', s₂⟩
    rw [e2] at hr
    rcases r' with _ | _ | _ <;> cases hr
  · cases hr
    exact h tb s _ _ e

theorem RRet.ite' {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {x y : R α}
    (h₁ : c → RRet P x) (h₂ : ¬ c → RRet P y) : RRet P (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

theorem RRet.dite' {α : Type} {P : α → Prop} {c : Prop} [Decidable c] {x : c → R α} {y : ¬ c → R α}
    (h₁ : ∀ hc, RRet P (x hc)) (h₂ : ∀ hc, RRet P (y hc)) : RRet P (if hc : c then x hc else y hc) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h₁ hc
  · rw [dif_neg hc]; exact h₂ hc

theorem RRet.mapM' {α β : Type} {P : β → Prop} {f : α → R β} (h : ∀ a, RRet P (f a)) :
    ∀ (l : List α), RRet (fun r => ∀ b ∈ r, P b) (l.mapM f) := by
  intro l
  induction l with
  | nil => exact RRet.pure' (fun _ hb => by cases hb)
  | cons a as ih =>
    rw [List.mapM_cons]
    refine RRet.bind_of (h a) fun b hb => RRet.bind_of ih fun bs hbs => RRet.pure' ?_
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hb
    · exact hbs y hy


theorem RRet.forIn' {α β : Type} (I : β → Prop) {xs : List α} {init : β} {f : α → β → R (ForInStep β)}
    (h0 : I init) (hf : ∀ x ∈ xs, ∀ b, I b → RRet (fun r => I r.value) (f x b)) : RRet I (forIn xs init f) := by
  induction xs generalizing init with
  | nil => rw [List.forIn_nil]; exact RRet.pure' h0
  | cons a as ih =>
    rw [List.forIn_cons]
    refine RRet.bind_of (hf a (List.mem_cons_self ..) init h0) fun r hr => ?_
    cases r with
    | done b => exact RRet.pure' hr
    | yield b => exact ih hr fun x hx b hb => hf x (List.mem_cons_of_mem _ hx) b hb

/-! ## No embedded value: `resolveF` and `bindersF` -/

/-- A term holds no embedded value (`Term.val`), the form `Knot.FieldsNoVal` and `Assembly.ParamsNoVal` ask. -/
def NoValT (t : Term) : Prop := t.anyAtom (fun _ => true) = false

theorem anyAtomList_noVal {l : List Term} (h : ∀ t ∈ l, t.anyAtom (fun _ => true) = false) :
    Term.anyAtomList (fun _ => true) l = false := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [Term.anyAtomList, Bool.or_eq_false_iff]
    exact ⟨h a (List.mem_cons_self ..), ih fun t ht => h t (List.mem_cons_of_mem _ ht)⟩

theorem anyAtomArms_noVal {l : List (Hint × Term)} (h : ∀ x ∈ l, x.2.anyAtom (fun _ => true) = false) :
    Term.anyAtomArms (fun _ => true) l = false := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨_, t⟩ := a
    simp only [Term.anyAtomArms, Bool.or_eq_false_iff]
    exact ⟨h _ (List.mem_cons_self ..), ih fun t ht => h t (List.mem_cons_of_mem _ ht)⟩


theorem anyAtomArms_noVal' {l : List (Hint × Term)} (h : ∀ a b, (a, b) ∈ l → b.anyAtom (fun _ => true) = false) :
    Term.anyAtomArms (fun _ => true) l = false :=
  anyAtomArms_noVal fun x hx => h x.1 x.2 hx

theorem ofNat_noVal (n : Nat) : (Term.ofNat n).anyAtom (fun _ => true) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Term.ofNat, Term.anyAtom, ih]

/-- The walk of the resolver's code, goal first: a recursive call returns no embedded value (`ih`), every other
bound value is ignored, an error returns nothing, branches split; each `pure` is left. -/
macro "rret_walk" ih:ident : tactic => `(tactic| repeat (any_goals first
    | (refine RRet.bind_of ($ih.1 _ _ _) fun _ _ => ?_)
    | (refine RRet.bind_of (RRet.onFail' ($ih.1 _ _ _)) fun _ _ => ?_)
    | (refine RRet.bind_of (RRet.mapM' (fun _ => $ih.1 _ _ _) _) fun _ _ => ?_)
    | (refine RRet.bind_of ($ih.2 _ _) fun _ _ => ?_)
    | (refine RRet.map_of ($ih.1 _ _ _) fun _ _ => ?_)
    | (refine RRet.bind_of (RRet.forIn' (fun (o : Array (Hint × Term)) => ∀ x ∈ o.toList, NoValT x.2)
        (fun _ h => by cases h) (fun ⟨_, _, _, _⟩ _ _ _ => ?_)) fun _ _ => ?_)
    | (refine $ih.1 _ _ _)
    | (with_reducible apply RRet.throw')
    | (with_reducible apply RRet.exhausted')
    | (refine RRet.bind' fun _ => ?_)
    | (apply RRet.ite' <;> intro _)
    | (apply RRet.dite' <;> intro _)
    | (dsimp only)
    | (split)))

set_option maxHeartbeats 8000000 in
theorem noVal_resolveF : ∀ fuel : Nat,
    (∀ ctx ty t, RRet NoValT (resolveF fuel ctx ty t)) ∧
    (∀ ctx bs, RRet (fun r : Ctx × List Hint × List Term => ∀ d ∈ r.2.2, NoValT d) (bindersF fuel ctx bs)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun ctx ty t => ?_, fun ctx bs => ?_⟩
    · unfold resolveF; exact RRet.exhausted'
    · unfold bindersF
      split
      · exact RRet.pure' (fun _ h => by cases h)
      · exact RRet.exhausted'
  | succ n ih =>
    refine ⟨fun ctx ty t => ?_, fun ctx bs => ?_⟩
    · unfold resolveF
      rret_walk ih
      all_goals (try (apply RRet.pure'))
      all_goals (try (simp only [NoValT] at *))
      all_goals (try (simp_all [Term.anyAtom, Term.anyAtomList, Term.anyAtomArms, succFn, ofNat_noVal, anyAtomList_noVal,
        anyAtomArms_noVal, anyAtomArms_noVal']))
      all_goals first
        | (apply anyAtomArms_noVal'
           intro a b h
           have h' : (a, b) ∈ _ := Array.mem_toList_iff.mp h
           solve_by_elim)
        | (intro a b h
           rcases h with h | ⟨_, rfl⟩ <;> solve_by_elim)
        | (intro a b h
           solve_by_elim)
    · unfold bindersF
      split
      · exact RRet.pure' (fun _ h => by cases h)
      · refine RRet.bind_of (ih.1 _ _ _) fun A hA => RRet.bind_of (ih.2 _ _) fun r hr => RRet.pure' ?_
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hA
        · exact hr d hd

/-! ## No embedded value: `resolveDecl`, and a resolved program -/

/-- What `exists_dataModel` asks of an inductive item: no embedded value in a field or parameter type. -/
def ItemNoVal (it : Item) : Prop := ∀ d, it = .ind d → DataModel.Exists.Knot.FieldsNoVal d ∧ DataModel.Exists.Assembly.ParamsNoVal d

theorem RRet.throwBind {α β : Type} {P : β → Prop} {e : String} {f : α → R β} : RRet P ((throw e : R α) >>= f) :=
  RRet.bind_of (Q := fun _ => False) RRet.throw' fun _ h => h.elim

theorem itemNoVal_ind (n : String) (hs : List Hint) (ps : List Term) (srt : Nat) (cs' : List (String × List (String × Term)))
    (cp ab un : Bool) (hp : ∀ d ∈ ps, NoValT d) (hcs : ∀ c ∈ cs', ∀ f ∈ c.2, NoValT f.2) :
    ItemNoVal (.ind { name := n, params := hs.zip ps, sort := srt, ctors := cs', «copy» := cp, «abstract» := ab, «unsized» := un }) := by
  intro d hd
  cases hd
  refine ⟨fun c i FT hFT => ?_, fun j => ?_⟩
  · unfold fieldTerm at hFT
    simp only at hFT
    obtain ⟨⟨fn, FT'⟩, h1, h2⟩ := Option.map_eq_some_iff.1 hFT
    obtain ⟨⟨cn, fs⟩, h3, h4⟩ := Option.bind_eq_some_iff.1 h1
    simp only at h2
    subst h2
    exact hcs _ (List.mem_of_getElem? h3) _ (List.mem_of_getElem? h4)
  · unfold DataModel.Exists.Knot.paramTerm
    simp only
    cases e : (hs.zip ps)[j]? with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.getD_some]
      exact hp _ (List.of_mem_zip (List.mem_of_getElem? e)).2

theorem noVal_resolveDecl (sd : SDecl) (fuel : Nat) : RRet ItemNoVal (resolveDecl sd fuel) := by
  unfold resolveDecl Surface.binders Surface.resolve
  have hF := noVal_resolveF fuel
  split
  · rename_i cs _
    dsimp only
    split
    · exact RRet.throwBind
    · refine RRet.bind_of (hF.2 [] _) fun r hr => ?_
      obtain ⟨ctx', hs, ps⟩ := r
      dsimp only
      refine RRet.bind_of (Q := fun cs' : List (String × List (String × Term)) => ∀ c ∈ cs', ∀ f ∈ c.2, NoValT f.2)
        (RRet.mapM' (P := fun c : String × List (String × Term) => ∀ f ∈ c.2, NoValT f.2) (fun x => ?_) _) fun cs' hcs => ?_
      · obtain ⟨cn, fs⟩ := x
        dsimp only
        refine RRet.bind_of (RRet.mapM' (P := fun f : String × Term => NoValT f.2) (fun y => ?_) _) fun l hl => RRet.pure' hl
        obtain ⟨fname, FT⟩ := y
        exact RRet.bind_of (hF.1 _ _ _) fun t ht => RRet.pure' ht
      · split <;> first
          | exact itemNoVal_ind _ _ _ _ _ _ _ _ hr hcs
          | exact RRet.throwBind
          | exact RRet.pure' (itemNoVal_ind _ _ _ _ _ _ _ _ hr hcs)
  · dsimp only
    repeat (any_goals first
      | exact RRet.throwBind
      | exact RRet.pure' (fun d h => by cases h)
      | (refine RRet.bind' fun _ => ?_)
      | (apply RRet.ite' <;> intro _)
      | (split)
      | (dsimp only))

/-- **A resolved item holds no embedded value in a field or parameter type** (`Surface.runResolve`,
the run `checkProgram` makes, at any fuel and recording flag). -/
theorem noVal_runResolve (p : List SDecl) (sd : SDecl) (fuel : Nat) (record : Bool) {it : Item}
    (h : (runResolve p sd fuel record).1 = .ok (.ok it)) : ItemNoVal it := by
  have := noVal_resolveDecl sd fuel
  unfold RRet at this
  exact this (Tables.ofProgram p) { record := record } it (runResolve p sd fuel record).2 (by
    show runResolve p sd fuel record = _
    rw [← h])

/-! ## No embedded value in a definition's types and body (exists13, for `NamesFact`) -/

/-- What `NamesFact` asks of a definition item: no embedded value in a parameter type, the codomain or the body. -/
def DefNoVal (it : Item) : Prop := ∀ d, it = .defn d → (∀ x ∈ d.doms, NoValT x) ∧ NoValT d.cod ∧ NoValT d.body

theorem noValDef_resolveDecl (sd : SDecl) (fuel : Nat) : RRet DefNoVal (resolveDecl sd fuel) := by
  unfold resolveDecl Surface.binders Surface.resolve
  have hF := noVal_resolveF fuel
  split
  · dsimp only
    repeat (any_goals first
      | exact RRet.throwBind
      | exact RRet.pure' (fun d h => by cases h)
      | (refine RRet.bind' fun _ => ?_)
      | (apply RRet.ite' <;> intro _)
      | (split)
      | (dsimp only))
  · dsimp only
    split
    · exact RRet.throwBind
    · refine RRet.bind_of (hF.2 _ _) fun r hr => ?_
      refine RRet.bind_of (hF.1 _ _ _) fun cod hcod => ?_
      apply RRet.ite' <;> intro _
      all_goals
        refine RRet.bind_of (hF.1 _ _ _) fun body hbody => RRet.bind' fun dec => RRet.pure' ?_
        intro d hd
        cases hd
        exact ⟨hr, hcod, hbody⟩

/-- **A resolved definition holds no embedded value** in its parameter types, codomain or body. -/
theorem noValDef_runResolve (p : List SDecl) (sd : SDecl) (fuel : Nat) (record : Bool) {it : Item}
    (h : (runResolve p sd fuel record).1 = .ok (.ok it)) : DefNoVal it := by
  have := noValDef_resolveDecl sd fuel
  unfold RRet at this
  exact this (Tables.ofProgram p) { record := record } it (runResolve p sd fuel record).2 (by
    show runResolve p sd fuel record = _
    rw [← h])

end Ochr.Meaning.Steps.Machine
