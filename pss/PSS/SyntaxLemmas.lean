import PSS.Syntax

/-!
# Syntax lemmas

Closedness lemmas for shift and substitution.
-/

open Expr

theorem Expr.shift_closedAt_gen {s : Expr} {d c n : Nat}
    (hle : c ≤ n)
    (hs : s.closedAt n = true) : (s.shift d c).closedAt (n + d) = true := by
  induction s generalizing c n with
  | bvar k =>
    simp only [Expr.closedAt, decide_eq_true_eq] at hs
    simp only [Expr.shift]
    split
    · next h =>
      simp only [Expr.closedAt, decide_eq_true_eq]
      omega
    · next h =>
      simp only [Expr.closedAt, decide_eq_true_eq]
      omega
  | top => rfl
  | lam dom body ih_dom ih_body =>
    simp only [Expr.shift, Expr.closedAt, Bool.and_eq_true] at *
    constructor
    · exact ih_dom hle hs.1
    · have : n + d + 1 = n + 1 + d := by omega
      rw [this]
      exact ih_body (by omega) hs.2
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
        · next hgt =>
          simp only [Expr.closedAt, decide_eq_true_eq]
          omega
        · next hle =>
          simp only [Expr.closedAt, decide_eq_true_eq]
          omega
    | top => rfl
    | lam dom bd ih_dom ih_body =>
      simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at *
      exact ⟨ih_dom hb.1 hs hjn,
             ih_body hb.2 (Expr.shift_closedAt hs) (by omega)⟩
    | app f a ih_f ih_a =>
      simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at *
      exact ⟨ih_f hb.1 hs hjn, ih_a hb.2 hs hjn⟩
