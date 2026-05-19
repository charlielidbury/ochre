import PSS.Syntax

/-!
# Syntax lemmas

Shift/subst algebra: commutation, cancellation, closedness.
-/

open Expr

/-! ## Basic shift lemmas -/

theorem Expr.shift_zero (e : Expr) (c : Nat) : e.shift 0 c = e := by
  induction e generalizing c with
  | bvar k => simp only [Expr.shift]; split <;> simp
  | top => rfl
  | lam dom body ih_dom ih_body => simp [Expr.shift, ih_dom, ih_body]
  | app f a ih_f ih_a => simp [Expr.shift, ih_f, ih_a]

theorem Expr.shift_shift (e : Expr) (d d' c : Nat) :
    (e.shift d c).shift d' c = e.shift (d + d') c := by
  induction e generalizing c with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hkc : k < c
    · simp only [if_pos hkc, Expr.shift, if_pos hkc]
    · simp only [if_neg hkc, Expr.shift, if_neg (show ¬ (k + d < c) by omega), if_neg hkc]
      congr 1; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.lam (ih_dom c)) (ih_body (c + 1))
  | app f a ih_f ih_a =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.app (ih_f c)) (ih_a c)

theorem Expr.shift_succ_zero (v : Expr) (j : Nat) :
    (v.shift j 0).shift 1 0 = v.shift (j + 1) 0 := by
  rw [Expr.shift_shift]

/-! ## Shift commutation -/

theorem Expr.shift_comm (e : Expr) (d1 d2 c1 c2 : Nat) (h : c1 ≤ c2) :
    (e.shift d2 c2).shift d1 c1 = (e.shift d1 c1).shift d2 (c2 + d1) := by
  induction e generalizing c1 c2 with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hk2 : k < c2
    · simp only [if_pos hk2, Expr.shift]
      by_cases hk1 : k < c1
      · simp only [if_pos hk1, Expr.shift, if_pos (show k < c2 + d1 by omega)]
      · simp only [if_neg hk1, Expr.shift, if_pos (show k + d1 < c2 + d1 by omega)]
    · simp only [if_neg hk2, Expr.shift, if_neg (show ¬(k + d2 < c1) by omega)]
      by_cases hk1 : k < c1
      · simp only [if_pos hk1, Expr.shift, if_neg (show ¬(k < c2 + d1) by omega)]
        congr 1; omega
      · simp only [if_neg hk1, Expr.shift, if_neg (show ¬(k + d1 < c2 + d1) by omega)]
        congr 1; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift]
    have hd := ih_dom c1 c2 h
    have hb := ih_body (c1 + 1) (c2 + 1) (by omega)
    simp only [show c2 + 1 + d1 = c2 + d1 + 1 from by omega] at hb
    exact congr (congrArg Expr.lam hd) hb
  | app f a ih_f ih_a =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.app (ih_f c1 c2 h)) (ih_a c1 c2 h)

theorem Expr.shift_shift_of_le (e : Expr) (n d c c0 : Nat) (h : c ≤ n) :
    (e.shift n c0).shift d (c0 + c) = e.shift (n + d) c0 := by
  induction e generalizing c0 with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hk : k < c0
    · simp only [if_pos hk, Expr.shift, if_pos (show k < c0 + c by omega)]
    · simp only [if_neg hk, Expr.shift, if_neg (show ¬(k + n < c0 + c) by omega), if_neg hk]
      congr 1; omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift]
    have hb := ih_body (c0 + 1)
    simp only [show c0 + 1 + c = c0 + c + 1 from by omega] at hb
    exact congr (congrArg Expr.lam (ih_dom c0)) hb
  | app f a ih_f ih_a =>
    simp only [Expr.shift]
    exact congr (congrArg Expr.app (ih_f c0)) (ih_a c0)

/-! ## Shift / substitution interaction -/

theorem Expr.shift_subst_cancel (e s : Expr) (c : Nat) :
    (e.shift 1 c).subst c s = e := by
  induction e generalizing s c with
  | bvar k =>
    simp only [Expr.shift]
    by_cases hk : k < c
    · simp only [if_pos hk, Expr.subst, beq_iff_eq,
                  if_neg (show ¬(k = c) by omega), if_neg (show ¬(k > c) by omega)]
    · simp only [if_neg hk, Expr.subst, beq_iff_eq,
                  if_neg (show ¬(k + 1 = c) by omega), if_pos (show k + 1 > c by omega)]
      show Expr.bvar (k + 1 - 1) = Expr.bvar k
      simp [Nat.add_sub_cancel]
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.lam (ih_dom s c)) (ih_body (s.shift 1 0) (c + 1))
  | app f a ih_f ih_a =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.app (ih_f s c)) (ih_a s c)

theorem Expr.shift_subst_comm (e s : Expr) (d c j : Nat) (hle : j ≤ c) :
    (e.subst j s).shift d c = (e.shift d (c + 1)).subst j (s.shift d c) := by
  induction e generalizing s c j with
  | bvar k =>
    simp only [Expr.subst, beq_iff_eq]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, Expr.shift, if_pos (show k < c + 1 by omega),
                  Expr.subst, beq_iff_eq, ite_true]
    · by_cases hkj' : k > j
      · simp only [if_neg hkj, if_pos hkj']
        by_cases hkc : k - 1 < c
        · simp only [Expr.shift, if_pos hkc, if_pos (show k < c + 1 by omega),
                      Expr.subst, beq_iff_eq, if_neg hkj, if_pos hkj']
        · simp only [Expr.shift, if_neg hkc, if_neg (show ¬(k < c + 1) by omega),
                      Expr.subst, beq_iff_eq,
                      if_neg (show ¬(k + d = j) by omega), if_pos (show k + d > j by omega)]
          congr 1; omega
      · simp only [if_neg hkj, if_neg (show ¬(k > j) by omega),
                    Expr.shift, if_pos (show k < c by omega), if_pos (show k < c + 1 by omega),
                    Expr.subst, beq_iff_eq, if_neg hkj, if_neg (show ¬(k > j) by omega)]
  | top => simp [Expr.subst, Expr.shift]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.subst]
    have hd := ih_dom s c j hle
    have hb := ih_body (s.shift 1 0) (c + 1) (j + 1) (by omega)
    -- Goal has (s.shift d c).shift 1 0, IH has (s.shift 1 0).shift d (c+1)
    -- By shift_comm: (s.shift d c).shift 1 0 = (s.shift 1 0).shift d (c + 1)
    rw [Expr.shift_comm s 1 d 0 c (Nat.zero_le _)]
    exact congr (congrArg Expr.lam hd) hb
  | app f a ih_f ih_a =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.app (ih_f s c j hle)) (ih_a s c j hle)

theorem Expr.shift_subst_comm_ge (e s : Expr) (d c j : Nat) (hge : c ≤ j) :
    (e.subst j s).shift d c = (e.shift d c).subst (j + d) (s.shift d c) := by
  induction e generalizing s c j with
  | bvar k =>
    simp only [Expr.subst, beq_iff_eq]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, Expr.shift, if_neg (show ¬(k < c) by omega),
                  Expr.subst, beq_iff_eq, ite_true]
    · by_cases hkj' : k > j
      · simp only [if_neg hkj, if_pos hkj',
                    Expr.shift, if_neg (show ¬(k - 1 < c) by omega),
                    if_neg (show ¬(k < c) by omega),
                    Expr.subst, beq_iff_eq,
                    if_neg (show ¬(k + d = j + d) by omega),
                    if_pos (show k + d > j + d by omega)]
        congr 1; omega
      · simp only [if_neg hkj, if_neg (show ¬(k > j) by omega)]
        by_cases hkc : k < c
        · simp only [Expr.shift, if_pos hkc, Expr.subst, beq_iff_eq,
                      if_neg (show ¬(k = j + d) by omega), if_neg (show ¬(k > j + d) by omega)]
        · simp only [Expr.shift, if_neg hkc, Expr.subst, beq_iff_eq,
                      if_neg (show ¬(k + d = j + d) by omega), if_neg (show ¬(k + d > j + d) by omega)]
  | top => simp [Expr.subst, Expr.shift]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.subst]
    have hd := ih_dom s c j hge
    have hb := ih_body (s.shift 1 0) (c + 1) (j + 1) (by omega)
    rw [Expr.shift_comm s 1 d 0 c (Nat.zero_le _), show j + d + 1 = j + 1 + d from by omega]
    exact congr (congrArg Expr.lam hd) hb
  | app f a ih_f ih_a =>
    simp only [Expr.shift, Expr.subst]
    exact congr (congrArg Expr.app (ih_f s c j hge)) (ih_a s c j hge)

/-! ## Substitution / substitution commutation -/

theorem Expr.subst_subst_comm_gen (e arg v : Expr) (i j : Nat) :
    (e.subst i (arg.shift i 0)).subst (i + j) (v.shift i 0) =
    (e.subst (i + j + 1) (v.shift (i + 1) 0)).subst i ((arg.subst j v).shift i 0) := by
  induction e generalizing arg v i j with
  | bvar k =>
    simp only [Expr.subst, beq_iff_eq]
    by_cases hki : k = i
    · -- k = i: inner subst → arg.shift i 0; outer subst on RHS → (arg.subst j v).shift i 0
      rw [if_pos hki, hki]
      rw [if_neg (show ¬(i = i + j + 1) by omega), if_neg (show ¬(i > i + j + 1) by omega)]
      -- RHS: (bvar i).subst i ((arg.subst j v).shift i 0) = (arg.subst j v).shift i 0
      simp only [Expr.subst, beq_iff_eq, if_pos rfl]
      -- LHS: (arg.shift i 0).subst (i+j) (v.shift i 0) = (arg.subst j v).shift i 0
      rw [Expr.shift_subst_comm_ge arg v i 0 j (Nat.zero_le _)]
      congr 1; omega
    · rw [if_neg hki]
      by_cases hki_gt : k > i
      · rw [if_pos hki_gt]
        by_cases hkij1 : k = i + j + 1
        · -- k = i+j+1
          rw [hkij1]
          simp only [Expr.subst, beq_iff_eq,
                      if_pos (show i + j + 1 - 1 = i + j from by omega),
                      ite_true]
          -- Goal: v.shift i 0 = (v.shift (i+1) 0).subst i ((arg.subst j v).shift i 0)
          have : v.shift (i + 1) 0 = (v.shift i 0).shift 1 i := by
            -- (v.shift i 0).shift 1 i = (v.shift 1 0).shift i (0 + i) by shift_comm
            -- = (v.shift 1 0).shift i 0 = v.shift (1 + i) 0 by shift_shift
            have hc := Expr.shift_comm v i 1 0 0 (Nat.zero_le _)
            simp only [Nat.zero_add] at hc  -- hc : (v.shift 1 0).shift i 0 = (v.shift i 0).shift 1 i
            rw [← hc, Expr.shift_shift, show 1 + i = i + 1 from by omega]
          rw [this, Expr.shift_subst_cancel]
        · rw [if_neg hkij1]
          by_cases hkij1_gt : k > i + j + 1
          · -- Both sides reduce to bvar (k-2)
            simp only [Expr.subst, beq_iff_eq,
                        if_neg (show ¬(k - 1 = i + j) by omega),
                        if_pos (show k - 1 > i + j by omega),
                        if_pos hkij1_gt,
                        if_neg (show ¬(k - 1 = i) by omega),
                        if_pos (show k - 1 > i by omega)]
          · simp only [Expr.subst, beq_iff_eq,
                        if_neg (show ¬(k - 1 = i + j) by omega),
                        if_neg (show ¬(k - 1 > i + j) by omega),
                        if_neg (show ¬(k > i + j + 1) by omega),
                        if_neg hki, if_pos hki_gt]
      · rw [if_neg (show ¬(k > i) by omega)]
        simp only [Expr.subst, beq_iff_eq,
                    if_neg (show ¬(k = i + j) by omega), if_neg (show ¬(k > i + j) by omega),
                    if_neg (show ¬(k = i + j + 1) by omega), if_neg (show ¬(k > i + j + 1) by omega),
                    if_neg hki, if_neg (show ¬(k > i) by omega)]
  | top => simp [Expr.subst]
  | lam dom body ih_dom ih_body =>
    simp only [Expr.subst]
    -- Rewrite double shifts in the goal to single shifts
    rw [Expr.shift_shift arg i 1 0, Expr.shift_shift v i 1 0,
        Expr.shift_shift v (i + 1) 1 0, Expr.shift_shift (arg.subst j v) i 1 0]
    have hd := ih_dom arg v i j
    have hb := ih_body arg v (i + 1) j
    simp only [show i + 1 + j = i + j + 1 from by omega,
               show i + 1 + j + 1 = i + j + 1 + 1 from by omega] at hb
    exact congr (congrArg Expr.lam hd) hb
  | app f a ih_f ih_a =>
    simp only [Expr.subst]
    exact congr (congrArg Expr.app (ih_f arg v i j)) (ih_a arg v i j)

theorem Expr.subst_subst_comm_zero (e arg v : Expr) (j : Nat) :
    (e.subst 0 arg).subst j v =
    (e.subst (j + 1) (v.shift 1 0)).subst 0 (arg.subst j v) := by
  have h := Expr.subst_subst_comm_gen e arg v 0 j
  simp only [Expr.shift_zero, Nat.zero_add] at h; exact h

/-! ## Closedness lemmas -/

theorem Expr.shift_closedAt_gen {s : Expr} {d c n : Nat}
    (hle : c ≤ n) (hs : s.closedAt n = true) : (s.shift d c).closedAt (n + d) = true := by
  induction s generalizing c n with
  | bvar k =>
    simp only [Expr.closedAt, decide_eq_true_eq] at hs
    simp only [Expr.shift]; split <;> simp only [Expr.closedAt, decide_eq_true_eq] <;> omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.closedAt, Bool.and_eq_true] at *
    exact ⟨ih_dom hle hs.1, by rw [show n + d + 1 = n + 1 + d from by omega]; exact ih_body (by omega) hs.2⟩
  | app f a ih_f ih_a =>
    simp only [Expr.shift, Expr.closedAt, Bool.and_eq_true] at *
    exact ⟨ih_f hle hs.1, ih_a hle hs.2⟩

theorem Expr.shift_closedAt {s : Expr} {n : Nat}
    (hs : s.closedAt n = true) : (s.shift 1 0).closedAt (n + 1) = true :=
  Expr.shift_closedAt_gen (Nat.zero_le _) hs

theorem Expr.subst_closedAt_zero {body s : Expr}
    (hb : body.closedAt 1 = true) (hs : s.closedAt 0 = true) :
    (body.subst 0 s).closedAt 0 = true :=
  aux hb hs (Nat.zero_le _)
where
  aux {body s : Expr} {j n : Nat}
      (hb : body.closedAt (n + 1) = true) (hs : s.closedAt n = true)
      (hjn : j ≤ n) :
      (body.subst j s).closedAt n = true := by
    induction body generalizing j n s with
    | bvar k =>
      simp only [Expr.closedAt, decide_eq_true_eq] at hb
      simp only [Expr.subst]
      split
      · exact hs
      · next hne =>
        simp only [beq_iff_eq] at hne
        split
        · next hgt => simp only [Expr.closedAt, decide_eq_true_eq]; omega
        · next hle => simp only [Expr.closedAt, decide_eq_true_eq]; omega
    | top => rfl
    | lam dom bd ih_dom ih_body =>
      simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at *
      exact ⟨ih_dom hb.1 hs hjn, ih_body hb.2 (Expr.shift_closedAt hs) (by omega)⟩
    | app f a ih_f ih_a =>
      simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at *
      exact ⟨ih_f hb.1 hs hjn, ih_a hb.2 hs hjn⟩
