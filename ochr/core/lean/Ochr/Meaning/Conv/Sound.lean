import Ochr.Meaning.Conv.Hyps

/-!
# N3 for values that hold no code and no constructor value (conv1, 2026-11-28)

Part A of the old attempt (`Rules/SoundT.lean`), re-proved on today's model: the strict type formers
(`EqOk`, `paramsOk`), the claim in the consumers' form (`Alike`: `NoProp` and `Fit` at one hint and
type), for the class `Plain` of values with no code (no closure, Π-closure or sealed program) and no
constructor value. Constructor values are left out here: their fields are typed by the data model's
`readTy`, which types nothing at a junk leaf (`DataModel.shapeReadTy`), so their congruence needs the
records of the types compared to have no junk leaf (`DataModel.RecLeafOk`; the canonical records of
a faithful model have none, `Faithful.leafOk`); see the report's "for the theory".
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Steps Ochr.Meaning.DataModel

/-- **Plain values**: built from atoms by `S`, `&`, a borrow, a mark, `Eq` and an inductive type
applied to plain arguments. No code, no constructor value. -/
inductive Plain : Value → Prop
  | zero : Plain .zero
  | unit : Plain .unit
  | gfn (n : String) : Plain (.gfn n)
  | loan (l : Nat) : Plain (.loan l)
  | bot : Plain .bot
  | abs (s : Nat) : Plain (.abs s)
  | proof : Plain .proof
  | tNat : Plain .tNat
  | tUnit : Plain .tUnit
  | sort (l : Nat) : Plain (.sort l)
  | succ {a : Value} : Plain a → Plain (.succ a)
  | tRef {a : Value} : Plain a → Plain (.tRef a)
  | borrow {l : Nat} {a : Value} : Plain a → Plain (.borrow l a)
  | gloan {l : Nat} {a : Value} : Plain a → Plain (.gloan l a)
  | tEq {A a b : Value} : Plain A → Plain a → Plain b → Plain (.tEq A a b)
  | tInd {n : String} {as : List Value} : (∀ a ∈ as, Plain a) → Plain (.tInd n as)

mutual
/-- On plain values `==` is equality (it ignores only binder names and recorded parameters, which
occur only in code and in constructor values). -/
theorem Plain.beq_eq : ∀ {v w : Value}, Plain v → Value.beq v w = true → v = w
  | .zero, w, _, h | .unit, w, _, h | .bot, w, _, h | .proof, w, _, h | .tNat, w, _, h
  | .tUnit, w, _, h => by cases w <;> simp_all [Value.beq]
  | .gfn _, w, _, h | .loan _, w, _, h | .abs _, w, _, h | .sort _, w, _, h => by
    cases w <;> simp_all [Value.beq]
  | .succ a, w, .succ pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h
    rw [Plain.beq_eq pa h]
  | .tRef a, w, .tRef pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true] at h
    rw [Plain.beq_eq pa h]
  | .borrow l a, w, .borrow pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Plain.beq_eq pa h]
  | .gloan l a, w, .gloan pa, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Plain.beq_eq pa h]
  | .tEq A a b, w, .tEq pA pa pb, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Plain.beq_eq pA h1, Plain.beq_eq pa h2, Plain.beq_eq pb h3]
  | .tInd n as, w, .tInd pas, h => by
    cases w <;> simp only [Value.beq, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [Plain.beqList_eq pas h]

theorem Plain.beqList_eq : ∀ {as bs : List Value}, (∀ a ∈ as, Plain a) → Value.beqList as bs = true → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [Value.beqList] at h
  | _ :: _, [], _, h => by simp [Value.beqList] at h
  | a :: as, b :: bs, pas, h => by
    simp only [Value.beqList, Bool.and_eq_true] at h
    rw [Plain.beq_eq (pas a (List.mem_cons_self ..)) h.1,
      Plain.beqList_eq (fun x hx => pas x (List.mem_cons_of_mem _ hx)) h.2]
end

theorem Plain.mkAnd {p q : Value} (hp : Plain p) (hq : Plain q) : Plain (Ochr.mkAnd p q) := by
  unfold Ochr.mkAnd
  split
  · exact hq
  · exact hp
  · exact .tInd fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hp
      · exact hq

theorem Plain.unitTop : ∀ (v : Value), Plain v → Plain (unitTop v) := by
  intro v
  induction v using unitTop.induct with
  | case1 p q ihp ihq =>
    intro h
    rw [Ochr.unitTop]
    cases h with
    | tInd hs => exact Plain.mkAnd (ihp (hs p (by simp))) (ihq (hs q (by simp)))
  | case2 v hv => intro h; rw [Ochr.unitTop.eq_2 v hv]; exact h

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem Alike.rfl' (v : Value) : Alike K ρ φ v v := fun _ _ _ _ _ _ => rfl

/-! ### The congruence of each plain former, for the claim -/

theorem alike_succ {a b : Value} (ih : Alike K ρ φ a b) : Alike K ρ φ (.succ a) (.succ b) := by
  intro h T na nb fa fb
  have fa' := succ_fit fa
  have fb' := succ_fit fb
  show (meanV K ρ φ (.plain TyM.nat) a).succ = (meanV K ρ φ (.plain TyM.nat) b).succ
  rw [ih _ _ na nb (.inr (.inl fa')) (.inr (.inl fb'))]

theorem alike_tRef {A B : Value} (ih : Alike K ρ φ A B) : Alike K ρ φ (.tRef A) (.tRef B) :=
  fun _ T na nb fa fb => ih (.plain TyM.err) T na nb fa fb

theorem alike_borrow {l : Nat} {a b : Value} (ih : Alike K ρ φ a b) :
    Alike K ρ φ (.borrow l a) (.borrow l b) :=
  fun h T na nb fa fb => ih h T na nb fa fb

theorem alike_gloan {l : Nat} {a b : Value} (ih : Alike K ρ φ a b) :
    Alike K ρ φ (.gloan l a) (.gloan l b) :=
  fun h T na nb fa fb => ih h T na nb fa fb

/-- An equation type: its type at the error hint (a type with a level), its sides at its type. -/
theorem alike_tEq {A a b B c d : Value} (iA : Alike K ρ φ A B) (ia : Alike K ρ φ a c)
    (ib : Alike K ρ φ b d) : Alike K ρ φ (.tEq A a b) (.tEq B c d) := by
  intro h T n1 n2 f1 f2
  obtain ⟨nA, na, nb⟩ := n1
  obtain ⟨nB, nc, nd⟩ := n2
  rw [meanV_tEq'] at f1 f2 ⊢
  by_cases hok1 : EqOk K.dm.read (meanV K ρ φ (.plain .err) A) (meanV K ρ φ (.plain (capTy K ρ φ A)) a)
      (meanV K ρ φ (.plain (capTy K ρ φ A)) b)
  · by_cases hok2 : EqOk K.dm.read (meanV K ρ φ (.plain .err) B) (meanV K ρ φ (.plain (capTy K ρ φ B)) c)
        (meanV K ρ φ (.plain (capTy K ρ φ B)) d)
    · obtain ⟨hl1, sa, sb⟩ := id hok1
      obtain ⟨hl2, sc, sd⟩ := id hok2
      obtain ⟨X, hX, hXl⟩ := ty_of_asTy_level hl1
      obtain ⟨Y, hY, hYl⟩ := ty_of_asTy_level hl2
      have eA : meanV K ρ φ (.plain .err) A = meanV K ρ φ (.plain .err) B :=
        iA (.plain .err) TyM.err nA nB (.inr (.inr ⟨rfl, X, hX, hXl⟩)) (.inr (.inr ⟨rfl, Y, hY, hYl⟩))
      have eT : capTy K ρ φ A = capTy K ρ φ B := by unfold capTy; rw [eA]
      replace sa : SideOk K.dm.read (capTy K ρ φ A) _ := sa
      replace sb : SideOk K.dm.read (capTy K ρ φ A) _ := sb
      replace sc : SideOk K.dm.read (capTy K ρ φ B) _ := sc
      replace sd : SideOk K.dm.read (capTy K ρ φ B) _ := sd
      rw [eT] at sa sb ⊢
      have e1 := ia (.plain (capTy K ρ φ B)) (capTy K ρ φ B) na nc (fit_of_side sa) (fit_of_side sc)
      have e2 := ib (.plain (capTy K ρ φ B)) (capTy K ρ φ B) nb nd (fit_of_side sb) (fit_of_side sd)
      rw [eA, e1, e2, meanV_tEq']
    · rw [if_neg hok2] at f2; exact absurd f2 ty_err_not_fit
  · rw [if_neg hok1] at f1; exact absurd f1 ty_err_not_fit

/-- Alike parameters mean alike, each at its parameter type at the earlier ones. -/
theorem meanParams_alike (d : IndDecl) : ∀ (as bs : List Value) (i : Nat) (e : List Sem),
    AlikeL K ρ φ as bs → NoPropL K as → NoPropL K bs →
    POk K.dm d i e (meanParams K ρ φ d i e as) → POk K.dm d i e (meanParams K ρ φ d i e bs) →
    meanParams K ρ φ d i e as = meanParams K ρ φ d i e bs
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _, _, _, _ => h.elim
  | _ :: _, [], _, _, h, _, _, _, _ => h.elim
  | a :: as, b :: bs, i, e, ⟨hab, hrest⟩, ⟨na, nas⟩, ⟨nb, nbs⟩, pa, pb => by
    obtain ⟨m1, pa'⟩ := POk.cons (m := meanV K ρ φ (.plain (K.dm.paramTy d i e)) a) pa
    obtain ⟨m2, pb'⟩ := POk.cons (m := meanV K ρ φ (.plain (K.dm.paramTy d i e)) b) pb
    have e1 := hab _ _ na nb (.inr (.inl m1)) (.inr (.inl m2))
    show meanV K ρ φ (.plain (K.dm.paramTy d i e)) a :: meanParams K ρ φ d (i + 1)
        (e ++ [meanV K ρ φ (.plain (K.dm.paramTy d i e)) a]) as =
      meanV K ρ φ (.plain (K.dm.paramTy d i e)) b :: meanParams K ρ φ d (i + 1)
        (e ++ [meanV K ρ φ (.plain (K.dm.paramTy d i e)) b]) bs
    rw [e1] at pa' ⊢
    rw [meanParams_alike d as bs (i + 1) _ hrest nas nbs pa' pb']

/-- An inductive type applied to arguments: each argument at its parameter type. -/
theorem alike_tInd {n : String} {as bs : List Value} (ih : AlikeL K ρ φ as bs) :
    Alike K ρ φ (.tInd n as) (.tInd n bs) := by
  intro h T n1 n2 f1 f2
  rcases meanV_tInd_cases K ρ φ h n as with he | ⟨d, hd, hp1⟩
  · rw [he] at f1; exact absurd f1 ty_err_not_fit
  rcases meanV_tInd_cases K ρ φ h n bs with he | ⟨d', hd', hp2⟩
  · rw [he] at f2; exact absurd f2 ty_err_not_fit
  rw [hd] at hd'
  cases hd'
  have e := meanParams_alike d as bs 0 [] ih n1 n2 (pOk_of_paramsOk hp1) (pOk_of_paramsOk hp2)
  simp only [meanV, hd, if_pos hp1, if_pos hp2, e]

end

/-! ### (A) for plain values: a derivation in the machine's instance makes them alike -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {G : Premises} {gs : List GDef}

/-- The unit laws applied to both sides keep the claim. -/
theorem alike_of_unitTop (hu : UnitOk K ρ φ Plain) {v w : Value} (pv : Plain v) (pw : Plain w)
    (ih : Alike K ρ φ (unitTop v) (unitTop w)) : Alike K ρ φ v w := by
  intro h T nv nw fv fw
  obtain ⟨nv', ev⟩ := hu.keep h T v pv nv fv
  obtain ⟨nw', ew⟩ := hu.keep h T w pw nw fw
  rw [← ev, ← ew]
  exact ih h T nv' nw' (ev ▸ fv) (ew ▸ fw)

mutual
/-- **N3 for plain values** (part A): a derivation of `v ≡ w` in the machine's instance, both plain,
makes them alike, given [Conv-fun]'s premise (only it can fire between plain values: two globals)
and the unit laws. -/
theorem convV_alike_plain (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ Plain) :
    ∀ {v w : Value}, ConvV Syn.machine G gs v w → Plain v → Plain w → Alike K ρ φ v w
  | _, _, .refl h, pv, _ => by rw [pv.beq_eq h]; exact Alike.rfl' _
  | _, _, .unit _ _ d, pv, pw =>
    alike_of_unitTop hu pv pw (convH_alike_plain hp hu d (pv.unitTop) (pw.unitTop))

theorem convH_alike_plain (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ Plain) :
    ∀ {v w : Value}, ConvH Syn.machine G gs v w → Plain v → Plain w → Alike K ρ φ v w
  | _, _, .refl h, pv, _ => by rw [pv.beq_eq h]; exact Alike.rfl' _
  | _, _, .succ d, .succ pa, .succ pb => alike_succ (convV_alike_plain hp hu d pa pb)
  | _, _, .tRef d, .tRef pa, .tRef pb => alike_tRef (convV_alike_plain hp hu d pa pb)
  | _, _, .tInd d, .tInd pa, .tInd pb => alike_tInd (convL_alike_plain hp hu d pa pb)
  | _, _, .tEq d1 d2 d3, .tEq p1 p2 p3, .tEq q1 q2 q3 =>
    alike_tEq (convV_alike_plain hp hu d1 p1 q1) (convV_alike_plain hp hu d2 p2 q2)
      (convV_alike_plain hp hu d3 p3 q3)
  | _, _, .borrow d, .borrow pa, .borrow pb => alike_borrow (convV_alike_plain hp hu d pa pb)
  | _, _, .ind _ _, pv, _ => nomatch pv
  | _, _, .sealed _, pv, _ => nomatch pv
  | _, _, .piCong _ _ _, pv, _ => nomatch pv
  | _, _, .pi _, pv, _ => nomatch pv
  | _, _, .fn _ _ _ _ _ _ h, _, _ => hp _ _ h

theorem convL_alike_plain (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ Plain) :
    ∀ {as bs : List Value}, ConvL Syn.machine G gs as bs → (∀ a ∈ as, Plain a) → (∀ b ∈ bs, Plain b) →
      AlikeL K ρ φ as bs
  | _, _, .nil, _, _ => trivial
  | _, _, .cons d ds, pa, pb =>
    ⟨convV_alike_plain hp hu d (pa _ (List.mem_cons_self ..)) (pb _ (List.mem_cons_self ..)),
      convL_alike_plain hp hu ds (fun a h => pa a (List.mem_cons_of_mem _ h))
        (fun b h => pb b (List.mem_cons_of_mem _ h))⟩
end

end

end Ochr.Meaning.Conv
