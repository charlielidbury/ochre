import Ochr.Meaning.Conv.Sound
import Ochr.Meaning.Conv.RefineEq

/-!
# `Eq` computes soundly, on plain sides (conv1, 2026-11-28)

Part A for `Eq` (the old `Rules/SoundEq.lean`) on today's model, for plain sides: if `Eq(A, a, b)`
computes to `P` by the rules (`EqTo`, the machine's instance), its sides plain, `⊥` or members of
`⟦A⟧`, and `⟦A⟧` a type with a level, then `P` means `⟦a⟧ = ⟦b⟧` at `⟦A⟧`, at every hint. Rules:
[Eq-disj] at `⊥`, [Eq-refl] (by N3 for plain values), [Eq-inj] at `S`, [Eq-disj] at `Z`/`S`,
[Eq-stuck]. [Eq-inj] at a constructor value does not arise between plain sides.
-/

namespace Ochr.Meaning.Conv
open Ochr Ochr.Meaning Ochr.Meaning.Strict Ochr.Meaning.Steps Ochr.Meaning.DataModel

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- A meaning uniform over hints. -/
def PropU (P : Value) (p : Prop) : Prop := ∀ hint, meanV K ρ φ hint P = .ty (TyM.prop p)

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

theorem mem_ne_moved {s : Sem} {T : TyM} (h : s ∈ₛ[K.dm.read] T) : s ≠ .moved := by
  intro e; have := mem_whole K.dm.read_wholeFields h; rw [e] at this; simp [Sem.whole] at this

/-- `S` of a meaning is whole only at a number. -/
theorem sem_succ_num {x : Sem} (h : x.succ.whole) : ∃ n, x = .el0 Nat n := by
  unfold Sem.succ at h
  cases hx : x.asNat with
  | some n => exact ⟨n, eq_of_asNat hx⟩
  | none =>
    rw [hx] at h
    simp only at h
    by_cases hw : x.whole
    · rw [if_pos hw] at h; simp [Sem.whole] at h
    · rw [if_neg hw] at h
      simp only [Sem.whole, List.mem_singleton, forall_eq] at h
      exact absurd h hw

theorem sem_succ_el0 (n : Nat) : (Sem.el0 Nat n).succ = .el0 Nat (n + 1) := by
  simp [Sem.succ, Sem.asNat, Sem.as]

/-- A side `S(x)` of an equation is a member, so `x` means a number (read at `Nat`). -/
theorem side_succ_num {T : TyM} {x : Value} (h : SideOkV K ρ φ T (.succ x)) :
    ∃ n, meanV K ρ φ (.plain TyM.nat) x = .el0 Nat n := by
  rcases h with h | h
  · cases h
  · exact sem_succ_num (mem_whole K.dm.read_wholeFields h)

theorem side_of_num {x : Value} {n : Nat} (hn : meanV K ρ φ (.plain TyM.nat) x = .el0 Nat n) :
    SideOkV K ρ φ (capTy K ρ φ .tNat) x :=
  .inr (by show meanV K ρ φ (.plain TyM.nat) x ∈ₛ[K.dm.read] TyM.nat; rw [hn]; exact ⟨n, rfl⟩)

theorem fit_of_sideV {T : TyM} {a : Value} (h : SideOkV K ρ φ T a) : Fit K.dm.read T (meanV K ρ φ (.plain T) a) := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr (.inl h)

theorem beq_bot_iff (a : Value) : Value.beq a .bot = true ↔ a = .bot := by
  cases a <;> simp [Value.beq]

theorem sideOk_of_sideV {T : TyM} {a : Value} (h : SideOkV K ρ φ T a) :
    SideOk K.dm.read T (meanV K ρ φ (.plain T) a) := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr h

theorem disj_plain_absurd {T : TyM} {a b : Value} (pa : Plain a) (hd : distinctCtors a b = true)
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
  | ind => cases pa
  | _ => simp [distinctCtors] at hd

theorem capTy_tNat : capTy K ρ φ .tNat = TyM.nat := rfl

end

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future} {G : Premises} {gs : List GDef} {Γ : List IndDecl}

mutual
/-- **`Eq` computes soundly, on plain sides**: if `Eq(A, a, b)` computes to `P` by the rules (the
machine's instance), its sides plain, holding no `Prop` constructor value, each `⊥` or a member of
`⟦A⟧`, and `⟦A⟧` a type with a level, then `P` means `⟦a⟧ = ⟦b⟧` at `⟦A⟧`, at every hint. Assumes
[Conv-fun]'s premise (for [Eq-refl]), the unit laws, and the library's connectives (`LibOk`). -/
theorem eqTo_plain (hp : PremFn K ρ φ G) (hu : UnitOk K ρ φ Plain) (hl : LibOk K ρ φ) :
    ∀ {A a b P : Value}, EqTo Syn.machine G gs Γ A a b P → Plain a → Plain b → NoProp K a → NoProp K b →
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
    rw [hl.tru hint, convV_alike_plain hp hu d pa pb _ _ na nb (fit_of_sideV sa) (fit_of_sideV sb)]
    congr 2
    exact propext ⟨fun _ => rfl, fun _ => trivial⟩
  | A, .succ a', .succ b', P, .succ d, .succ pa, .succ pb, na, nb, sa, sb, _ => by
    obtain ⟨n, hn⟩ := side_succ_num sa
    obtain ⟨m, hm⟩ := side_succ_num sb
    have ih := eqTo_plain hp hu hl d pa pb na nb (side_of_num hn) (side_of_num hm) rfl
    intro hint
    rw [ih hint]
    congr 2
    show (meanV K ρ φ (.plain TyM.nat) a' = meanV K ρ φ (.plain TyM.nat) b') =
      ((meanV K ρ φ (.plain TyM.nat) a').succ = (meanV K ρ φ (.plain TyM.nat) b').succ)
    rw [hn, hm, sem_succ_el0, sem_succ_el0]
    exact propext ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  | _, _, _, _, .inj .., pa, _, _, _, _, _, _ => nomatch pa
  | A, a, b, _, .disj hd, pa, pb, _, _, sa, sb, _ => fun hint => by
    rw [hl.fls hint]
    congr 2
    refine propext ⟨False.elim, fun e => ?_⟩
    exact disj_plain_absurd pa hd sa sb e
  | A, a, b, _, .stuck, _, _, _, _, sa, sb, hA => fun hint => by
    rw [meanV_tEq', if_pos ⟨hA, sideOk_of_sideV sa, sideOk_of_sideV sb⟩]

theorem eqL_plain_triv : ∀ {Ts vs ws Ps : List Value}, EqL Syn.machine G gs Γ Ts vs ws Ps → True
  | _, _, _, _, _ => trivial
end

end

end Ochr.Meaning.Conv
