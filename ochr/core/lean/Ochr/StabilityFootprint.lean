import Ochr.StabilitySig

/-!
# Stability: the footprint (field `footprint` of `DecisionsCommute`)

A footprint reads two things: the terms' free places (`Term.freeOccs`) and, for each binding
of the top frame such a place is rooted at, its *borrow profile*: whether its stored type is a
borrow type, whether its value is a borrow (and then the owners of that borrow's loan) or `⊥`.
This file proves that a refinement keeps the free places (it substitutes into embedded values,
never into places), and that the footprint is monotone in the borrow profile
(`footprint_mono`). So the field reduces to one invariant, that a refinement can only shrink a
binding's borrow profile (`ProfileLE`), which is not proved here (`notes/stability.md` §9).

The last part shows, against the real checker, why `Respects` asks for borrow-free values and why
`ValueDeclCommutes` (D55 preservation) is a property of checked programs only.
-/

namespace Ochr.Stability
open Ochr

/-! ## Substitution keeps a term's free places -/

/-- `substT` over a list keeps every list reading of free places, and the length. -/
def OccsList (ds' ds : List Term) : Prop :=
  ds'.length = ds.length ∧ (∀ c, Term.placeOccsList c ds' = Term.placeOccsList c ds) ∧
    (∀ c, Term.placeOccsDoms c ds' = Term.placeOccsDoms c ds)

theorem occsList_mapM (f : Term → M Term) (hf : ∀ t, Post (f t) (fun t' => ∀ c, t'.placeOccs c = t.placeOccs c)) :
    ∀ ds : List Term, Post (ds.mapM f) (fun ds' => OccsList ds' ds)
  | [] => by simpa using Post.pure (P := fun ds' => OccsList ds' []) ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  | d :: ds => by
    rw [List.mapM_cons]
    refine Post.bind (hf d) fun d' hd => Post.bind (occsList_mapM f hf ds) fun ds' ⟨hl, h1, h2⟩ => Post.pure ?_
    refine ⟨by simp [hl], fun c => ?_, fun c => ?_⟩
    · simp only [Term.placeOccsList, hd, h1]
    · simp only [Term.placeOccsDoms, hd, h2]

theorem occsArms_mapM (f : Term → M Term) (hf : ∀ t, Post (f t) (fun t' => ∀ c, t'.placeOccs c = t.placeOccs c)) :
    ∀ as : List (Hint × Term), Post (as.mapM fun (h, a) => do pure (h, ← f a))
      (fun as' => ∀ c, Term.placeOccsArms c as' = Term.placeOccsArms c as)
  | [] => by simpa using Post.pure (P := fun as' => ∀ c, Term.placeOccsArms c as' = Term.placeOccsArms c []) fun _ => rfl
  | (h, a) :: as => by
    rw [List.mapM_cons]
    refine Post.bind (Post.bind (hf a) fun a' ha => Post.pure (P := fun (p : Hint × Term) => p.1 = h ∧ ∀ c, p.2.placeOccs c = a.placeOccs c) ⟨rfl, ha⟩)
      fun p ⟨hp1, hp2⟩ => Post.bind (occsArms_mapM f hf as) fun as' has => Post.pure fun c => ?_
    obtain ⟨h', a'⟩ := p
    simp only [Term.placeOccsArms, hp2, has]

/-- Substitution keeps a term's free places: it rewrites embedded values, never places. -/
theorem substT_occs (x r : Value) : ∀ (fuel : Nat) (t : Term),
    Post (substT fuel x r t) (fun t' => ∀ c, t'.placeOccs c = t.placeOccs c)
  | 0, t => by unfold substT; exact Post.exhausted _
  | n + 1, t => by
    have ih := substT_occs x r n
    have hl := occsList_mapM _ ih
    have ha := occsArms_mapM _ ih
    unfold substT
    simp only []
    refine Post.ite _ (Post.pure fun _ => rfl) ?_
    split <;>
      (repeat (first
        | (refine Post.bind (ih _) fun _ _ => ?_)
        | (refine Post.bind (hl _) fun _ _ => ?_)
        | (refine Post.bind (ha _) fun _ _ => ?_)
        | (refine Post.bind_any fun _ => ?_))) <;>
      exact Post.pure fun c => by simp_all [Term.placeOccs, OccsList]

theorem onTerm_occs (α : Refinement) (fuel : Nat) (t : Term) :
    Post (α.onTerm fuel t) (fun t' => ∀ c, t'.placeOccs c = t.placeOccs c) := by
  unfold Refinement.onTerm
  exact Post.foldlM _ (fun t' => ∀ c, t'.placeOccs c = t.placeOccs c)
    (fun u p hu => (substT_occs _ p.2 fuel u).mono fun u' h c => (h c).trans (hu c)) α t (fun _ => rfl)

theorem freeOccs_eq {t t' : Term} (h : ∀ c, t'.placeOccs c = t.placeOccs c) : t'.freeOccs = t.freeOccs := by
  simp only [Term.freeOccs, h]

/-! ## The footprint is monotone in the borrow profile -/

instance : LawfulBEq Pos where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> simp_all [BEq.beq, instBEqPos.beq]
  rfl {a} := by cases a <;> simp [BEq.beq, instBEqPos.beq]

/-- Two lists related elementwise. -/
inductive Pairwise2 {α α' : Type} (S : α → α' → Prop) : List α → List α' → Prop
  | nil : Pairwise2 S [] []
  | cons {a a' l l'} : S a a' → Pairwise2 S l l' → Pairwise2 S (a :: l) (a' :: l')

theorem Pairwise2.refl {α : Type} : ∀ l : List α, Pairwise2 (· = ·) l l
  | [] => .nil
  | _ :: l => .cons rfl (Pairwise2.refl l)

theorem forIn_rel {α α' β γ : Type} (S : α → α' → Prop) (R : β → γ → Prop)
    (f : α → β → Id (ForInStep β)) (g : α' → γ → Id (ForInStep γ))
    (hf : ∀ a b, ∃ b', Id.run (f a b) = ForInStep.yield b') (hg : ∀ a c, ∃ c', Id.run (g a c) = ForInStep.yield c')
    (hstep : ∀ a a' b c, S a a' → R b c → R (Id.run (f a b)).value (Id.run (g a' c)).value) :
    ∀ (l : List α) (l' : List α'), Pairwise2 S l l' → ∀ b c, R b c →
      R (Id.run (forIn l b f)) (Id.run (forIn l' c g))
  | [], [], .nil, b, c, h => h
  | a :: l, a' :: l', .cons hs hl, b, c, h => by
    obtain ⟨b', hb⟩ := hf a b
    obtain ⟨c', hc⟩ := hg a' c
    have := hstep a a' b c hs h
    rw [hb, hc] at this
    simp only [List.forIn_cons, Id.run] at hb hc ⊢
    rw [show f a b = ForInStep.yield b' from hb, show g a' c = ForInStep.yield c' from hc]
    exact forIn_rel S R f g hf hg hstep l l' hl b' c' this

theorem mem_dedup (L : List Pos) : ∀ (out : List Pos) (q : Pos),
    q ∈ Id.run (forIn L out fun q s =>
      if s.contains q = true then pure (ForInStep.yield s) else pure (ForInStep.yield (s ++ [q]))) ↔
      q ∈ out ∨ q ∈ L := by
  induction L with
  | nil => intro out q; simp
  | cons a L ih =>
    intro out q
    simp only [List.forIn_cons]
    by_cases ha : out.contains a = true
    · simp only [ha, ↓reduceIte]
      have hmem : a ∈ out := by simpa using ha
      rw [show ∀ x, (pure (ForInStep.yield out) >>= x : Id _) = x (ForInStep.yield out) from fun _ => rfl]
      simp only [ih, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hmem)
        · exact Or.inr h
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      rw [show ∀ x, (pure (ForInStep.yield (out ++ [a])) >>= x : Id _) = x (ForInStep.yield (out ++ [a])) from
        fun _ => rfl]
      simp only [ih, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

theorem mem_dedup' (L out : List Pos) (q : Pos) :
    q ∈ (Id.run (do
      let s ← forIn L out fun q s =>
        if s.contains q = true then pure (ForInStep.yield s) else pure (ForInStep.yield (s ++ [q]))
      pure (ForInStep.yield s))).value ↔ q ∈ out ∨ q ∈ L :=
  mem_dedup L out q

theorem mem_ite_dedup (c : Bool) (L out : List Pos) (q : Pos) :
    q ∈ (Id.run (if c = true then (do
      let s ← forIn L out fun q s =>
        if s.contains q = true then pure (ForInStep.yield s) else pure (ForInStep.yield (s ++ [q]))
      pure (ForInStep.yield s)) else pure (ForInStep.yield out))).value ↔ q ∈ out ∨ (c = true ∧ q ∈ L) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, or_false]; rfl
  · simp only [↓reduceIte, true_and]; exact mem_dedup' L out q

/-- Whether a binding's stored type is a borrow type (as `footprint` reads it). -/
def refTyOf (b : Binding) : Bool := match b.ty with | some (.tRef _) => true | _ => false

/-- The binding of the top frame a free variable `o` is rooted at. -/
def topBind (env : Env) (o : Nat) : Binding := env[env.size - 1]!.binds[env[env.size - 1]!.binds.size - 1 - o]!

/-- The owners a place rooted at `o` contributes (as `footprint` computes them). -/
def rootsOf (env : Env) (o : Nat) : List Pos :=
  match (topBind env o).val with
  | .borrow m _ => owners env m
  | .bot => if !refTyOf (topBind env o) then [.bind (env.size - 1) (env[env.size - 1]!.binds.size - 1 - o)] else []
  | _ => [.bind (env.size - 1) (env[env.size - 1]!.binds.size - 1 - o)]

/-- `env'`'s borrow profile is below `env`'s: the same top frame, and each of its bindings is a
borrow (by type or value) only if it was, with owners among the old ones. -/
structure ProfileLE (env' env : Env) : Prop where
  size : env'.size = env.size
  top : env'[env'.size - 1]!.binds.size = env[env.size - 1]!.binds.size
  refs : ∀ o, o < env[env.size - 1]!.binds.size →
    (refTyOf (topBind env' o) || (topBind env' o).val.isBorrow) = true →
      (refTyOf (topBind env o) || (topBind env o).val.isBorrow) = true
  roots : ∀ o, o < env[env.size - 1]!.binds.size → ∀ q ∈ rootsOf env' o, q ∈ rootsOf env o

/-- **The footprint is monotone in the borrow profile**, for terms with the same free places. -/
theorem footprint_mono {env env' : Env} {ts ts' : List Term}
    (hts : Pairwise2 (fun t' t => t'.freeOccs = t.freeOccs) ts' ts) (hp : ProfileLE env' env) :
    ∀ q ∈ footprint env' ts', q ∈ footprint env ts := by
  obtain ⟨hsize, htop, hrefs, hroots⟩ := hp
  simp only [refTyOf, topBind, rootsOf, hsize] at htop hrefs hroots
  simp only [htop] at hrefs hroots
  unfold footprint
  simp only [hsize, htop, bind_pure]
  refine forIn_rel (· = ·) (fun o' o => ∀ q ∈ o', q ∈ o) _ _ (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩) ?_
    _ _ (Pairwise2.refl _) [] [] (by simp)
  rintro writes _ out' out rfl hout
  refine forIn_rel (fun t' t => t'.freeOccs = t.freeOccs) (fun o' o => ∀ q ∈ o', q ∈ o) _ _
    (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩) ?_ _ _ hts out' out hout
  intro t' t out' out ht hout
  simp only [Id.run] at hout ⊢
  rw [ht]
  refine forIn_rel (· = ·) (fun o' o => ∀ q ∈ o', q ∈ o) _ _ ?_ ?_ ?_ _ _ (Pairwise2.refl _) out' out hout
  · intro occ s; repeat' split
    all_goals exact ⟨_, rfl⟩
  · intro occ s; repeat' split
    all_goals exact ⟨_, rfl⟩
  rintro ⟨o, pl, k⟩ _ out' out rfl hout q hq
  by_cases ho : o < env[env.size - 1]!.binds.size
  · simp only [ho, ↓reduceIte] at hq ⊢
    rw [mem_ite_dedup] at hq ⊢
    rcases hq with h | ⟨hc', h⟩
    · exact Or.inl (hout q h)
    · refine Or.inr ⟨?_, hroots o ho q h⟩
      cases writes <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hc' ⊢
      · exact ⟨hrefs o ho hc'.1, hc'.2⟩
      · exact hc'
  · simp only [ho, ↓reduceIte] at hq ⊢
    exact hout q hq

theorem onTerms_occs (α : Refinement) (fuel : Nat) : ∀ ts : List Term,
    Post (ts.mapM (α.onTerm fuel)) (fun tsα => Pairwise2 (fun t' t => t'.freeOccs = t.freeOccs) tsα ts)
  | [] => by simpa using Post.pure (P := fun tsα => Pairwise2 (fun (t' t : Term) => t'.freeOccs = t.freeOccs) tsα []) .nil
  | t :: ts => by
    rw [List.mapM_cons]
    exact Post.bind (onTerm_occs α fuel t) fun t' ht => Post.bind (onTerms_occs α fuel ts) fun ts' hts =>
      Post.pure (.cons (freeOccs_eq ht) hts)

/-- **Field `footprint`, reduced to the borrow profile.** If the refined state's borrow profile
is below the original's (`ProfileLE`), the footprint at the refined state is contained in the
original one. -/
theorem decisionsCommute_footprint (Ω : MState) (α : Refinement) (ts tsα : List Term) (fuel : Nat)
    (Ωα : MState) (hts : (run? (ts.mapM (α.onTerm fuel)) Ω fuel).map (·.1) = some tsα)
    (hp : ProfileLE Ωα.env Ω.env) : ∀ π ∈ footprint Ωα.env tsα, π ∈ footprint Ω.env ts := by
  obtain ⟨⟨a, Ω'⟩, hrun, ha⟩ := Option.map_eq_some_iff.mp hts
  simp only at ha; subst ha
  exact footprint_mono ((onTerms_occs α fuel ts).run? hrun) hp

/-! ## Why `Respects` asks for borrow-free values

Without it, refining `σ0 : Type` to `&Nat` makes a binding of type `σ0` borrow-typed, and a plain
read of it then counts toward the footprint, which grows. Checked against the real checker; the
value `&Nat` checks at `σ0`'s type, so only borrow-freeness excludes it. -/

/-- `σ0 : Type`, `σ1 : σ0`, and a binding `x : σ0` holding `σ1`. -/
def probeFpΩ : MState := { (default : MState) with
  absTy := #[.sort 1, .abs 0], nextAbs := 2,
  env := #[{ binds := #[{ hint := ⟨"x"⟩, ty := some (.abs 0), val := .abs 1 }] }] }

theorem probe_footprint_generic : (footprint probeFpΩ.env [.place (.var 0)] == []) = true := by
  decide +kernel
theorem probe_footprint_refined :
    ((run? (Refinement.onState [(0, .tRef .tNat)] 50) probeFpΩ 50).map
      (fun p => footprint p.2.env [.place (.var 0)]) == some [.bind 0 0]) = true := by
  decide +kernel
theorem probe_footprint_value_checks :
    ((run? (eval 50 true (.val (.tRef .tNat))) probeFpΩ 50).map (·.1) == some (.tRef .tNat, some (.sort 1))) = true := by
  decide +kernel
theorem probe_footprint_not_borrowFree : borrowFree (.tRef .tNat) = false := by decide +kernel

/-! ## D55 preservation needs checked globals (`ValueDeclCommutes`)

At a state whose globals were not checked, an embedded value's reading does not survive
refinement: `F (n : Nat) : Nat := Nat` is declared into `Nat` but returns a type. The sealed
program `⌈F(σ0)⌉` reads as data (`other`); refining `σ0 := Z` re-runs it to `Nat`, which reads as
a sort. So `ValueDeclCommutes` is a property of checked programs: evaluation preserves declared
readings, which needs an induction over the evaluator. -/

/-- `F (n : Nat) : Nat := Nat`, never checked. -/
def probeBadF : GDef := GDef.mk "F" (.tPi [] (.pi [⟨"n"⟩] [.nat] .nat))
  (some (.fix ⟨"F"⟩ [⟨"n"⟩] [.nat] .nat none .nat)) (.gfn "F") false []

def probeD55Ω : MState := { (default : MState) with
  absTy := #[.tNat], nextAbs := 1, globals := [probeBadF], env := #[{}] }

theorem probe_d55_generic :
    ((run? (valueDecl 50 (.sealed (.call (.val (.gfn "F")) [.val (.abs 0)] true))) probeD55Ω 50).map (·.1) ==
      some .other) = true := by decide +kernel
theorem probe_d55_refined :
    ((run? (Refinement.onValue [(0, .zero)] 50 (.sealed (.call (.val (.gfn "F")) [.val (.abs 0)] true)))
      probeD55Ω 50).map (·.1) == some .tNat) = true := by decide +kernel
theorem probe_d55_instance : ((run? (valueDecl 50 .tNat) probeD55Ω 50).map (·.1) == some (.sort 1)) = true := by
  decide +kernel

end Ochr.Stability
