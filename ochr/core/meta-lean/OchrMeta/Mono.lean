import OchrMeta.Interp

/-! # Fuel monotonicity of the clocked machine

`exec P n s t` either runs out of fuel (`oof`) or returns a result that no extra fuel changes
(`exec_mono`).  Corollaries: the machine is deterministic (`eval_det`), and `Eval` is exactly
"the interpreter `run` with enough fuel" (`eval_iff_run`).

The only fuel-consuming parts of `exec` are its recursive calls, direct or through the
evaluator parameter of `execArgs` and `callWith`; `access`, `popFrame`, `dropVal`, `takeTemps`
and `closeCall` use no fuel.  So the proof is one induction on the fuel, with the evaluator
lemmas `execArgs_agree` / `callWith_agree` stated for any pair of evaluators that agree
wherever the smaller one has not run out of fuel (`Agrees`). -/

namespace OchrMeta

/-- `ev'` agrees with `ev` wherever `ev` has not run out of fuel. -/
def Agrees (ev' ev : St → Term → Res) : Prop :=
  ∀ s t, ev s t ≠ .oof → ev' s t = ev s t

theorem Res.ne_oof_of_bind {r : Res} {k : St → Val → Res} (h : r.bind k ≠ .oof) : r ≠ .oof := by
  rintro rfl; exact h rfl

theorem execArgs_agree {ev' ev : St → Term → Res} (hev : Agrees ev' ev) :
    ∀ (args : List Term) (i : Nat) (s : St), execArgs ev i s args ≠ .oof →
      execArgs ev' i s args = execArgs ev i s args := by
  intro args
  induction args with
  | nil => intro i s _; rfl
  | cons a as ih =>
    intro i s h
    simp only [execArgs] at h ⊢
    rw [hev s a (Res.ne_oof_of_bind h)]
    cases hr : ev s a with
    | ok s' v => rw [hr] at h; exact ih (i + 1) _ h
    | _ => rfl

theorem callWith_agree {ev' ev : St → Term → Res} (hev : Agrees ev' ev) (cc : Bool) (f : String)
    (d : FunDef) (ws : List Val) (s : St) (h : callWith ev cc f d ws s ≠ .oof) :
    callWith ev' cc f d ws s = callWith ev cc f d ws s := by
  unfold callWith at h ⊢
  cases hb : d.body with
  | none => rfl
  | some b =>
    rw [hb] at h
    by_cases hl : ws.length = d.params.length
    · simp only [hl, if_true] at h ⊢
      have hne : ev (s.push (paramFrame d ws)) b ≠ .oof := by
        intro ho; rw [ho] at h; exact h rfl
      rw [hev _ _ hne]
    · simp only [hl, if_false]

/-- Fuel monotonicity: a run that does not run out of fuel is unchanged by more fuel. -/
theorem exec_mono (P : Prog) : ∀ (n k : Nat) (s : St) (t : Term),
    exec P n s t ≠ .oof → exec P (n + k) s t = exec P n s t := by
  intro n
  induction n with
  | zero => intro k s t h; exact absurd rfl h
  | succ n ih =>
    intro k s t h
    have hag : Agrees (exec P (n + k)) (exec P n) := fun s t => ih k s t
    rw [show n + 1 + k = (n + k) + 1 by omega]
    cases t with
    | read p => rfl
    | borrow p => rfl
    | assign p t =>
      simp only [exec] at h ⊢
      rw [hag s t (Res.ne_oof_of_bind h)]
    | letIn x t u =>
      simp only [exec] at h ⊢
      rw [hag s t (Res.ne_oof_of_bind h)]
      cases hr : exec P n s t with
      | ok s' v =>
        rw [hr] at h; simp only [Res.bind_ok] at h ⊢
        rw [hag _ u (Res.ne_oof_of_bind h)]
      | _ => rfl
    | seq t u =>
      simp only [exec] at h ⊢
      rw [hag s t (Res.ne_oof_of_bind h)]
      cases hr : exec P n s t with
      | ok s' v =>
        rw [hr] at h; simp only [Res.bind_ok] at h ⊢
        cases hd : dropVal .unit v s' with
        | none => rfl
        | some s'' => rw [hd] at h; simp only at h ⊢; exact hag _ u h
      | _ => rfl
    | zero => rfl
    | unit => rfl
    | succ t =>
      simp only [exec] at h ⊢
      rw [hag s t (Res.ne_oof_of_bind h)]
    | pair t u =>
      simp only [exec] at h ⊢
      rw [hag s t (Res.ne_oof_of_bind h)]
      cases hr : exec P n s t with
      | ok s' v =>
        rw [hr] at h; simp only [Res.bind_ok] at h ⊢
        rw [hag _ u (Res.ne_oof_of_bind h)]
      | _ => rfl
    | mtch p tz y ts =>
      simp only [exec] at h ⊢
      cases hr : access false p.root p.path s with
      | ok s' c =>
        rw [hr] at h; simp only [Res.bind_ok] at h ⊢
        cases c <;> simp only at h ⊢ <;> first | rfl | exact hag _ _ h
      | _ => rfl
    | call f args cc =>
      simp only [exec] at h ⊢
      cases hf : P.find f with
      | none => rfl
      | some d =>
        rw [hf] at h; simp only at h ⊢
        by_cases hp : d.ret = .prop
        · simp only [hp, if_true]
        · simp only [hp, if_false] at h ⊢
          rw [execArgs_agree hag args 0 s (Res.ne_oof_of_bind h)]
          cases hr : execArgs (exec P n) 0 s args with
          | ok s' v =>
            rw [hr] at h; simp only [Res.bind_ok] at h ⊢
            cases ht : takeTemps (List.range args.length) s' with
            | none => rfl
            | some q =>
              obtain ⟨ws, s''⟩ := q
              rw [ht] at h; simp only at h ⊢
              exact callWith_agree hag cc f d ws s'' h
          | _ => rfl
    | erase t => rfl

theorem exec_mono_le (P : Prog) {n m : Nat} (h : n ≤ m) {s : St} {t : Term}
    (hr : exec P n s t ≠ .oof) : exec P m s t = exec P n s t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact exec_mono P n k s t hr

/-- The machine is deterministic. -/
theorem eval_det {P : Prog} {s : St} {t : Term} {r₁ r₂ : Res}
    (h₁ : Eval P s t r₁) (h₂ : Eval P s t r₂) : r₁ = r₂ := by
  obtain ⟨hr₁, n₁, e₁⟩ := h₁
  obtain ⟨hr₂, n₂, e₂⟩ := h₂
  subst e₁ e₂
  rw [← exec_mono_le P (Nat.le_max_left n₁ n₂) hr₁, exec_mono_le P (Nat.le_max_right n₁ n₂) hr₂]

/-- `Eval` is exactly "the interpreter with enough fuel". -/
theorem eval_iff_run {P : Prog} {s : St} {t : Term} {r : Res} :
    Eval P s t r ↔ r ≠ .oof ∧ ∃ n, ∀ m, n ≤ m → run P m s t = r := by
  constructor
  · rintro ⟨hr, n, e⟩
    subst e
    exact ⟨hr, n, fun m hm => exec_mono_le P hm hr⟩
  · rintro ⟨hr, n, e⟩
    exact ⟨hr, n, e n (Nat.le_refl n)⟩

end OchrMeta
