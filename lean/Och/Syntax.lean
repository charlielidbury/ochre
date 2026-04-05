/-!
# Och Syntax (de Bruijn indices)

The core calculus has six term forms. Terms and types share a single syntactic
category — there is no separate type language.

Uses de Bruijn indices for bound variables. This eliminates capture issues in
substitution and makes alpha-equivalent terms syntactically identical.
-/

/-- Core syntax of Och with de Bruijn indices.

    e, τ ::=
      | n              — bound variable (de Bruijn index)
      | λτ. e          — lambda abstraction (domain + body, bvar 0 = param)
      | e₁ e₂         — application
      | (e : τ)        — ascription (precision loss)
      | Type           — universe / top
      | μτ. e          — unified self-reference (bvar 0 = self)
-/
inductive Expr where
  | bvar   : Nat → Expr
  | lam    : (dom : Expr) → (body : Expr) → Expr
  | app    : Expr → Expr → Expr
  | asc    : (term : Expr) → (ty : Expr) → Expr
  | type   : Expr
  | mu     : (ann : Expr) → (body : Expr) → Expr
deriving Inhabited, DecidableEq

namespace Expr

/-- Generate a variable name from a binding depth. -/
private def nameAt (idx : Nat) : String :=
  let letters := #["x", "y", "z", "w", "v", "u"]
  let base := letters[idx % letters.size]!
  if idx < letters.size then base else s!"{base}{idx / letters.size}"

/-- Pretty-print with human-readable variable names (inverse of the `och{…}` macro).
    `names` is the list of bound variable names (innermost-first, like de Bruijn).
    `prec` is the ambient precedence (higher = tighter context). -/
def pretty (e : Expr) (names : List String := []) (prec : Nat := 0) : String :=
  match e with
  | .type => "Type"
  | .bvar k => names.get? k |>.getD s!"?{k}"
  | .asc term ty =>
    s!"({term.pretty names 0} : {ty.pretty names 0})"
  | .lam dom body =>
    let n := nameAt names.length
    let s := s!"λ{n}:{dom.pretty names 10}. {body.pretty (n :: names) 0}"
    if prec > 10 then s!"({s})" else s
  | .mu ann body =>
    let n := nameAt names.length
    let s := s!"μ{n}:{ann.pretty names 10}. {body.pretty (n :: names) 0}"
    if prec > 10 then s!"({s})" else s
  | .app f a =>
    let s := s!"{f.pretty names 50} {a.pretty names 51}"
    if prec > 50 then s!"({s})" else s

instance : Repr Expr where
  reprPrec e _ := e.pretty

instance : ToString Expr where
  toString e := e.pretty

/-- Shift free variables with index ≥ c up by d. Used when going under
    binders to adjust indices for the new binding depth. -/
def shift (d c : Nat) : Expr → Expr
  | .bvar k => if k < c then .bvar k else .bvar (k + d)
  | .lam dom body => .lam (shift d c dom) (shift d (c + 1) body)
  | .app f a => .app (shift d c f) (shift d c a)
  | .asc term ty => .asc (shift d c term) (shift d c ty)
  | .type => .type
  | .mu ann body => .mu (shift d c ann) (shift d (c + 1) body)

/-- Substitute: replace bvar j with s in e. Indices > j are decremented by 1
    (the binder at j is being eliminated). s is shifted when going under
    binders so its free variables stay correct at the new depth. -/
def subst (e : Expr) (j : Nat) (s : Expr) : Expr :=
  match e with
  | .bvar k =>
    if k == j then s
    else if k > j then .bvar (k - 1)
    else .bvar k
  | .lam dom body => .lam (dom.subst j s) (body.subst (j + 1) (s.shift 1 0))
  | .app f a => .app (f.subst j s) (a.subst j s)
  | .asc term ty => .asc (term.subst j s) (ty.subst j s)
  | .type => .type
  | .mu ann body => .mu (ann.subst j s) (body.subst (j + 1) (s.shift 1 0))

/-- Generalized shift-subst cancellation: shifting by 1 at cutoff c then
    substituting at c is the identity, regardless of what value is substituted.
    After shifting, there are no bvar c's in the result, so the substitution
    value is never used. -/
theorem shift_subst_cancel_gen (e : Expr) (c : Nat) (s : Expr)
    : (e.shift 1 c).subst c s = e := by
  induction e generalizing c s with
  | bvar k =>
    unfold shift
    by_cases h : k < c
    · -- k < c: shift leaves bvar k
      simp [h, subst]
      -- Goal: (if k = c then s else if c < k then bvar (k-1) else bvar k) = bvar k
      have h1 : ¬ k = c := by omega
      have h2 : ¬ c < k := by omega
      simp [h1, h2]
    · -- k ≥ c: shift gives bvar (k+1)
      simp [h]
      show Expr.subst (.bvar (k + 1)) c s = .bvar k
      unfold Expr.subst
      -- Goal: (if k+1 = c then s else if c < k+1 then bvar k else bvar (k+1)) = bvar k
      have h1 : ¬ k + 1 = c := by omega
      have h2 : c < k + 1 := by omega
      simp [h1, h2]
  | lam dom body ih_dom ih_body =>
    unfold shift; unfold subst
    simp only [Expr.lam.injEq]
    exact ⟨ih_dom c s, ih_body (c + 1) (s.shift 1 0)⟩
  | app f a ih_f ih_a =>
    unfold shift; unfold subst
    simp only [Expr.app.injEq]
    exact ⟨ih_f c s, ih_a c s⟩
  | asc t y ih_t ih_y =>
    unfold shift; unfold subst
    simp only [Expr.asc.injEq]
    exact ⟨ih_t c s, ih_y c s⟩
  | type => rfl
  | mu ann body ih_ann ih_body =>
    unfold shift; unfold subst
    simp only [Expr.mu.injEq]
    exact ⟨ih_ann c s, ih_body (c + 1) (s.shift 1 0)⟩

/-- Shift-subst cancellation at cutoff 0 (common case). -/
theorem shift_subst_cancel (e : Expr) (s : Expr) : (e.shift 1 0).subst 0 s = e :=
  shift_subst_cancel_gen e 0 s

/-! ## Simultaneous substitution (for the fundamental theorem)

`substEnv γ e` simultaneously substitutes all free variables in `e` using
the environment `γ`. Variable `bvar i` (for i < γ.length) is replaced by
`γ[i]!`. Variables with index ≥ γ.length are shifted down by γ.length
(they become free in the outer scope).

This is needed for the fundamental theorem of the logical relation, where
soundness is proved for open terms with VCompat-related environments. -/

/-- Simultaneously substitute free variables using environment γ (partial).
    bvar i (i < γ.length) → γ[i]!
    bvar i (i ≥ γ.length) → bvar i  (identity — unchanged)
    Under binders, γ is lifted: bvar 0 ↦ bvar 0 (new param), rest shifted. -/
def substEnv (γ : List Expr) : Expr → Expr
  | .bvar k =>
    if k < γ.length then γ[k]!
    else .bvar k
  | .lam dom body =>
    .lam (substEnv γ dom) (substEnv ((.bvar 0) :: γ.map (·.shift 1 0)) body)
  | .app f a => .app (substEnv γ f) (substEnv γ a)
  | .asc term ty => .asc (substEnv γ term) (substEnv γ ty)
  | .type => .type
  | .mu ann body =>
    .mu (substEnv γ ann) (substEnv ((.bvar 0) :: γ.map (·.shift 1 0)) body)

/-- Identity environment at depth n: [bvar 0, bvar 1, ..., bvar (n-1)].
    Lifting: idEnv (n+1) = bvar 0 :: (idEnv n).map (shift 1 0). -/
def idEnv : Nat → List Expr
  | 0 => []
  | n + 1 => (.bvar 0) :: (idEnv n).map (·.shift 1 0)

private theorem idEnv_length (n : Nat) : (idEnv n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [idEnv, ih]

private theorem idEnv_getElem? (n k : Nat) (h : k < n) : (idEnv n)[k]? = some (.bvar k) := by
  induction n generalizing k with
  | zero => omega
  | succ m ih =>
    unfold idEnv
    cases k with
    | zero => simp [List.getElem?_cons_zero]
    | succ j =>
      simp [List.getElem?_cons_succ, List.getElem?_map]
      have hj : j < m := by omega
      rw [ih j hj]
      simp [shift]

private theorem lift_idEnv (n : Nat) :
    (.bvar 0 :: List.map (fun x => shift 1 0 x) (idEnv n)) = idEnv (n + 1) := by
  simp [idEnv]

/-- substEnv with any identity environment is the identity.
    Key lemma: the idEnv n entries satisfy (idEnv n)[k]? = some (bvar k) for k < n,
    and substEnv maps bvar k (k ≥ n) to bvar k. So all variables are preserved.
    The lam/mu cases use: bvar 0 :: (idEnv n).map (shift 1 0) = idEnv (n+1). -/
theorem substEnv_idEnv (n : Nat) (e : Expr) : substEnv (idEnv n) e = e := by
  induction e generalizing n with
  | bvar k =>
    unfold substEnv
    simp only [idEnv_length]
    by_cases h : k < n
    · simp [h, idEnv_getElem? n k h]
    · simp [h]
  | lam dom body ih_dom ih_body =>
    simp only [substEnv, lift_idEnv]
    congr 1
    · exact ih_dom n
    · exact ih_body (n + 1)
  | app f a ih_f ih_a =>
    simp only [substEnv]
    congr 1
    · exact ih_f n
    · exact ih_a n
  | asc t y ih_t ih_y =>
    simp only [substEnv]
    congr 1
    · exact ih_t n
    · exact ih_y n
  | type => rfl
  | mu ann body ih_ann ih_body =>
    simp only [substEnv, lift_idEnv]
    congr 1
    · exact ih_ann n
    · exact ih_body (n + 1)

/-- Empty environment is identity. Corollary of substEnv_idEnv at n=0. -/
theorem substEnv_nil (e : Expr) : substEnv [] e = e :=
  substEnv_idEnv 0 e

/-! ## Shift composition and identity -/

/-- Shifting by 0 is the identity. -/
@[simp] theorem shift_zero (e : Expr) (c : Nat) : e.shift 0 c = e := by
  induction e generalizing c with
  | bvar k => unfold shift; split <;> simp_all
  | lam d b ih_d ih_b =>
    show Expr.lam (d.shift 0 c) (b.shift 0 (c+1)) = .lam d b
    congr 1; exact ih_d c; exact ih_b (c+1)
  | app f a ih_f ih_a =>
    show Expr.app (f.shift 0 c) (a.shift 0 c) = .app f a
    congr 1; exact ih_f c; exact ih_a c
  | asc t y ih_t ih_y =>
    show Expr.asc (t.shift 0 c) (y.shift 0 c) = .asc t y
    congr 1; exact ih_t c; exact ih_y c
  | type => rfl
  | mu a b ih_a ih_b =>
    show Expr.mu (a.shift 0 c) (b.shift 0 (c+1)) = .mu a b
    congr 1; exact ih_a c; exact ih_b (c+1)

/-- Composing shifts at the same cutoff: shifting by d₂ then d₁ = shifting by d₁+d₂.
    Both shifts use the same cutoff c (the inner shift creates a gap at c,
    the outer shift extends it). Under binders, cutoff increments by 1 for both. -/
theorem shift_shift (e : Expr) (d1 d2 c : Nat) :
    (e.shift d2 c).shift d1 (c + d2) = e.shift (d1 + d2) c := by
  induction e generalizing c with
  | bvar k =>
    show (if k < c then Expr.bvar k else .bvar (k + d2)).shift d1 (c + d2) =
         if k < c then .bvar k else .bvar (k + (d1 + d2))
    split
    · rename_i h; show (Expr.bvar k).shift d1 (c + d2) = .bvar k
      unfold shift; simp [show k < c + d2 from by omega]
    · rename_i h; show (Expr.bvar (k + d2)).shift d1 (c + d2) = .bvar (k + (d1 + d2))
      unfold shift; simp [show ¬(k + d2 < c + d2) from by omega]; omega
  | lam dom body ih_dom ih_body =>
    show Expr.lam ((dom.shift d2 c).shift d1 (c + d2)) ((body.shift d2 (c+1)).shift d1 (c + d2 + 1)) =
         .lam (dom.shift (d1+d2) c) (body.shift (d1+d2) (c+1))
    congr 1; exact ih_dom c
    rw [show c + d2 + 1 = (c+1) + d2 from by omega]; exact ih_body (c + 1)
  | app f a ih_f ih_a =>
    show Expr.app ((f.shift d2 c).shift d1 (c+d2)) ((a.shift d2 c).shift d1 (c+d2)) =
         .app (f.shift (d1+d2) c) (a.shift (d1+d2) c)
    congr 1; exact ih_f c; exact ih_a c
  | asc t y ih_t ih_y =>
    show Expr.asc ((t.shift d2 c).shift d1 (c+d2)) ((y.shift d2 c).shift d1 (c+d2)) =
         .asc (t.shift (d1+d2) c) (y.shift (d1+d2) c)
    congr 1; exact ih_t c; exact ih_y c
  | type => rfl
  | mu ann body ih_ann ih_body =>
    show Expr.mu ((ann.shift d2 c).shift d1 (c+d2)) ((body.shift d2 (c+1)).shift d1 (c+d2+1)) =
         .mu (ann.shift (d1+d2) c) (body.shift (d1+d2) (c+1))
    congr 1; exact ih_ann c
    rw [show c + d2 + 1 = (c+1) + d2 from by omega]; exact ih_body (c + 1)

/-- Composing shifts at the SAME cutoff: (e.shift d₂ c).shift d₁ c = e.shift (d₁+d₂) c.
    Unlike shift_shift (which uses cutoff c+d₂ for the outer shift), this uses
    the same cutoff c for both. Valid because shift d₂ c produces no variables
    in [c, c+d₂), so the outer cutoff can be anywhere in that range. -/
theorem shift_shift_same (e : Expr) (d1 d2 c : Nat) :
    (e.shift d2 c).shift d1 c = e.shift (d1 + d2) c := by
  induction e generalizing c with
  | bvar k =>
    show (if k < c then Expr.bvar k else .bvar (k + d2)).shift d1 c =
         if k < c then .bvar k else .bvar (k + (d1 + d2))
    split
    · rename_i h; unfold shift; simp [h]
    · rename_i h; unfold shift; simp [show ¬(k + d2 < c) from by omega]; omega
  | lam dom body ih_dom ih_body =>
    show Expr.lam ((dom.shift d2 c).shift d1 c) ((body.shift d2 (c+1)).shift d1 (c+1)) =
         .lam (dom.shift (d1+d2) c) (body.shift (d1+d2) (c+1))
    congr 1; exact ih_dom c; exact ih_body (c+1)
  | app f a ih_f ih_a =>
    show Expr.app ((f.shift d2 c).shift d1 c) ((a.shift d2 c).shift d1 c) =
         .app (f.shift (d1+d2) c) (a.shift (d1+d2) c)
    congr 1; exact ih_f c; exact ih_a c
  | asc t y ih_t ih_y =>
    show Expr.asc ((t.shift d2 c).shift d1 c) ((y.shift d2 c).shift d1 c) =
         .asc (t.shift (d1+d2) c) (y.shift (d1+d2) c)
    congr 1; exact ih_t c; exact ih_y c
  | type => rfl
  | mu ann body ih_ann ih_body =>
    show Expr.mu ((ann.shift d2 c).shift d1 c) ((body.shift d2 (c+1)).shift d1 (c+1)) =
         .mu (ann.shift (d1+d2) c) (body.shift (d1+d2) (c+1))
    congr 1; exact ih_ann c; exact ih_body (c+1)

/-- Corollary: (s.shift c 0).shift 1 0 = s.shift (c+1) 0. -/
theorem shift_succ (s : Expr) (c : Nat) : (s.shift c 0).shift 1 0 = s.shift (c + 1) 0 := by
  have := shift_shift_same s 1 c 0; rw [Nat.add_comm] at this; exact this

/-! ## closedAt: scope predicate for free variables -/

/-- `closedAt n e` is true when all free variables in `e` have index < n.
    An expression is "closed at depth n" if it has at most n free variables. -/
def closedAt (n : Nat) : Expr → Bool
  | .bvar k => k < n
  | .lam dom body => closedAt n dom && closedAt (n + 1) body
  | .app f a => closedAt n f && closedAt n a
  | .asc term ty => closedAt n term && closedAt n ty
  | .type => true
  | .mu ann body => closedAt n ann && closedAt (n + 1) body

/-- Shifting preserves closedAt: if e has free vars < n, then
    e.shift d c has free vars < n + d (for c ≤ n). -/
theorem shift_closedAt (e : Expr) (n d c : Nat) (hc : c ≤ n)
    (h : closedAt n e = true) : closedAt (n + d) (e.shift d c) = true := by
  induction e generalizing n c with
  | bvar k =>
    simp only [shift]
    split
    · -- k < c: result is bvar k, need k < n + d
      simp only [closedAt, decide_eq_true_eq] at h ⊢; omega
    · -- k ≥ c: result is bvar (k + d), need k + d < n + d
      simp only [closedAt, decide_eq_true_eq] at h ⊢; omega
  | lam dom body ih_dom ih_body =>
    simp only [shift, closedAt, Bool.and_eq_true] at h ⊢
    refine ⟨ih_dom n c hc h.1, ?_⟩
    have := ih_body (n + 1) (c + 1) (by omega) h.2
    rwa [show n + 1 + d = n + d + 1 from by omega] at this
  | app f a ih_f ih_a =>
    simp only [shift, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨ih_f n c hc h.1, ih_a n c hc h.2⟩
  | asc t y ih_t ih_y =>
    simp only [shift, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨ih_t n c hc h.1, ih_y n c hc h.2⟩
  | type => simp [shift, closedAt]
  | mu ann body ih_ann ih_body =>
    simp only [shift, closedAt, Bool.and_eq_true] at h ⊢
    refine ⟨ih_ann n c hc h.1, ?_⟩
    have := ih_body (n + 1) (c + 1) (by omega) h.2
    rwa [show n + 1 + d = n + d + 1 from by omega] at this

/-- Substitution preserves closedAt (generalized over subst position j).
    closedAt (j+n+1) e ∧ closedAt (j+n) s → closedAt (j+n) (e.subst j s)
    Standard de Bruijn lemma. Uses shift_closedAt for the lam/mu binder cases
    where s gets shifted. -/
theorem subst_closedAt_gen (e : Expr) (j n : Nat) (s : Expr)
    (he : closedAt (j + n + 1) e = true) (hs : closedAt (j + n) s = true)
    : closedAt (j + n) (e.subst j s) = true := by
  induction e generalizing j s with
  | bvar k =>
    simp only [closedAt, decide_eq_true_eq] at he
    simp only [subst]
    by_cases heq : k == j
    · -- k = j: result is s
      simp only [heq, ↓reduceIte]; exact hs
    · -- k ≠ j
      simp only [heq, Bool.false_eq_true, ↓reduceIte]
      have hne : k ≠ j := by intro h; simp [h] at heq
      by_cases hgt : k > j
      · -- k > j: result is bvar (k - 1), need k - 1 < j + n
        simp [hgt, closedAt, decide_eq_true_eq]; omega
      · -- k < j (since k ≠ j and ¬(k > j)): result is bvar k, need k < j + n
        simp [hgt, closedAt, decide_eq_true_eq]; omega
  | type => simp [subst, closedAt]
  | lam dom body ih_dom ih_body =>
    simp only [closedAt, Bool.and_eq_true] at he
    obtain ⟨he_dom, he_body⟩ := he
    simp only [subst, closedAt, Bool.and_eq_true]
    refine ⟨ih_dom j s he_dom hs, ?_⟩
    have hshift : closedAt (j + 1 + n) (s.shift 1 0) = true := by
      have h1 := shift_closedAt s (j + n) 1 0 (Nat.zero_le _) hs
      have : j + n + 1 = j + 1 + n := by omega
      rw [this] at h1; exact h1
    have he2 : closedAt (j + 1 + n + 1) body = true := by
      have : (j + n + 1) + 1 = j + 1 + n + 1 := by omega
      rw [this] at he_body; exact he_body
    have := ih_body (j + 1) (s.shift 1 0) he2 hshift
    rwa [show j + 1 + n = j + n + 1 from by omega] at this
  | app f a ih_f ih_a =>
    simp only [closedAt, Bool.and_eq_true] at he
    obtain ⟨he_f, he_a⟩ := he
    simp only [subst, closedAt, Bool.and_eq_true]
    exact ⟨ih_f j s he_f hs, ih_a j s he_a hs⟩
  | asc t y ih_t ih_y =>
    simp only [closedAt, Bool.and_eq_true] at he
    obtain ⟨he_t, he_y⟩ := he
    simp only [subst, closedAt, Bool.and_eq_true]
    exact ⟨ih_t j s he_t hs, ih_y j s he_y hs⟩
  | mu ann body ih_ann ih_body =>
    simp only [closedAt, Bool.and_eq_true] at he
    obtain ⟨he_ann, he_body⟩ := he
    simp only [subst, closedAt, Bool.and_eq_true]
    refine ⟨ih_ann j s he_ann hs, ?_⟩
    have hshift : closedAt (j + 1 + n) (s.shift 1 0) = true := by
      have h1 := shift_closedAt s (j + n) 1 0 (Nat.zero_le _) hs
      have : j + n + 1 = j + 1 + n := by omega
      rw [this] at h1; exact h1
    have he2 : closedAt (j + 1 + n + 1) body = true := by
      have : (j + n + 1) + 1 = j + 1 + n + 1 := by omega
      rw [this] at he_body; exact he_body
    have := ih_body (j + 1) (s.shift 1 0) he2 hshift
    rwa [show j + 1 + n = j + n + 1 from by omega] at this

/-- Substitution at position 0 preserves closedAt.
    closedAt (n+1) e ∧ closedAt n s → closedAt n (e.subst 0 s) -/
theorem subst_closedAt {e s : Expr} {n : Nat}
    (he : closedAt (n + 1) e = true) (hs : closedAt n s = true)
    : closedAt n (e.subst 0 s) = true := by
  have := subst_closedAt_gen e 0 n s (by simpa using he) (by simpa using hs)
  simpa using this

/-! ## liftEnvN: iterated environment lifting -/

/-- Lift an environment c times (going under c binders).
    `liftEnvN 0 γ = γ`, `liftEnvN (c+1) γ = bvar 0 :: (liftEnvN c γ).map (shift 1 0)`.
    Entries: for i < c, bvar i; for i ≥ c, (γ[i-c]).shift c 0. -/
def liftEnvN : Nat → List Expr → List Expr
  | 0, γ => γ
  | c + 1, γ => (.bvar 0) :: (liftEnvN c γ).map (·.shift 1 0)

theorem liftEnvN_length (c : Nat) (γ : List Expr)
    : (liftEnvN c γ).length = c + γ.length := by
  induction c with
  | zero => simp [liftEnvN]
  | succ k ih => simp [liftEnvN, ih]; omega

/-- Entries of liftEnvN below the lifting depth are bvar i. -/
theorem liftEnvN_getElem?_lt (c : Nat) (γ : List Expr) (i : Nat) (h : i < c)
    : (liftEnvN c γ)[i]? = some (.bvar i) := by
  induction c generalizing i with
  | zero => omega
  | succ k ih =>
    simp [liftEnvN]
    cases i with
    | zero => simp [List.getElem?_cons_zero]
    | succ j =>
      simp [List.getElem?_cons_succ, List.getElem?_map]
      have hj : j < k := by omega
      rw [ih j hj]
      simp [shift]

/-! ## Shift-subst commutation -/

-- Generalized shift-subst commutation: shifting by 1 at cutoff d then
-- substituting at j+d+1 is the same as substituting at j+d then shifting.
-- Under binders, cutoff d and subst position both increment by 1,
-- and the subst value gains another shift 1 0 (composes to shift (d+1) 0).
set_option maxHeartbeats 2000000 in
theorem shift_subst_comm_gen (e : Expr) (j d : Nat) (t : Expr) :
    (e.shift 1 d).subst (j + d + 1) (t.shift (d + 1) 0)
    = (e.subst (j + d) (t.shift d 0)).shift 1 d := by
  induction e generalizing j d with
  | bvar k =>
    show (if k < d then Expr.bvar k else .bvar (k + 1)).subst (j + d + 1) (t.shift (d + 1) 0)
       = (if k == j + d then t.shift d 0 else if k > j + d then .bvar (k - 1) else .bvar k).shift 1 d
    by_cases hd : k < d
    · have h1 : ¬(k == j + d) = true := by simp; omega
      have h2 : ¬(k > j + d) := by omega
      simp only [if_pos hd, if_neg h1, show ¬(k > j + d) from h2, ite_false]
      unfold subst; simp [show ¬(k == j + d + 1) = true from by simp; omega,
                           show ¬(k > j + d + 1) from by omega]
      unfold shift; simp [hd]
    · by_cases h1 : k = j + d
      · simp only [if_neg hd, show (k == j + d) = true from by simp [beq_iff_eq]; exact h1, if_true]
        unfold subst; rw [h1]; simp
        have := shift_shift t 1 d 0; simp at this
        rw [show d + 1 = 1 + d from by omega]; exact this.symm
      · by_cases h2 : k > j + d
        · simp only [if_neg hd, show ¬(k == j + d) = true from by simp; exact h1,
                      if_neg (show ¬(k == j + d) = true from by simp; exact h1),
                      show k > j + d from h2, ite_true]
          unfold subst
          simp [show ¬(k + 1 == j + d + 1) = true from by simp; omega,
                show k + 1 > j + d + 1 from by omega]
          unfold shift; simp [show ¬(k - 1 < d) from by omega]; omega
        · have hlt : k < j + d := by omega
          simp only [if_neg hd, show ¬(k == j + d) = true from by simp; exact h1,
                      if_neg (show ¬(k == j + d) = true from by simp; exact h1),
                      show ¬(k > j + d) from h2, ite_false]
          unfold subst
          simp [show ¬(k + 1 == j + d + 1) = true from by simp; omega,
                show ¬(k + 1 > j + d + 1) from by omega]
          unfold shift; simp [show ¬(k < d) from hd]
  | type => rfl
  | lam dom body ih_dom ih_body =>
    show Expr.lam ((shift 1 d dom).subst (j + d + 1) (t.shift (d + 1) 0))
                  ((shift 1 (d + 1) body).subst (j + d + 2) ((t.shift (d + 1) 0).shift 1 0))
       = Expr.lam ((dom.subst (j + d) (t.shift d 0)).shift 1 d)
                  ((body.subst (j + d + 1) ((t.shift d 0).shift 1 0)).shift 1 (d + 1))
    congr 1
    · exact ih_dom j d
    · rw [show j + d + 2 = j + (d + 1) + 1 from by omega,
          shift_shift_same t 1 d 0, show 1 + d = d + 1 from by omega,
          shift_shift_same t 1 (d + 1) 0, show 1 + (d + 1) = d + 1 + 1 from by omega,
          show j + d + 1 = j + (d + 1) from by omega]
      exact ih_body j (d + 1)
  | app f a ih_f ih_a =>
    show Expr.app ((shift 1 d f).subst (j + d + 1) (t.shift (d + 1) 0))
                  ((shift 1 d a).subst (j + d + 1) (t.shift (d + 1) 0))
       = Expr.app ((f.subst (j + d) (t.shift d 0)).shift 1 d)
                  ((a.subst (j + d) (t.shift d 0)).shift 1 d)
    congr 1; exact ih_f j d; exact ih_a j d
  | asc tm ty ih_t ih_y =>
    show Expr.asc ((shift 1 d tm).subst (j + d + 1) (t.shift (d + 1) 0))
                  ((shift 1 d ty).subst (j + d + 1) (t.shift (d + 1) 0))
       = Expr.asc ((tm.subst (j + d) (t.shift d 0)).shift 1 d)
                  ((ty.subst (j + d) (t.shift d 0)).shift 1 d)
    congr 1; exact ih_t j d; exact ih_y j d
  | mu ann body ih_ann ih_body =>
    show Expr.mu ((shift 1 d ann).subst (j + d + 1) (t.shift (d + 1) 0))
                 ((shift 1 (d + 1) body).subst (j + d + 2) ((t.shift (d + 1) 0).shift 1 0))
       = Expr.mu ((ann.subst (j + d) (t.shift d 0)).shift 1 d)
                 ((body.subst (j + d + 1) ((t.shift d 0).shift 1 0)).shift 1 (d + 1))
    congr 1
    · exact ih_ann j d
    · rw [show j + d + 2 = j + (d + 1) + 1 from by omega,
          shift_shift_same t 1 d 0, show 1 + d = d + 1 from by omega,
          shift_shift_same t 1 (d + 1) 0, show 1 + (d + 1) = d + 1 + 1 from by omega,
          show j + d + 1 = j + (d + 1) from by omega]
      exact ih_body j (d + 1)

/-- Shift-subst commutation at cutoff 0: the standard de Bruijn lemma.
    Corollary of the generalized version at d=0. -/
theorem shift_subst_comm (e : Expr) (j : Nat) (t : Expr) :
    (e.shift 1 0).subst (j + 1) (t.shift 1 0) = (e.subst j t).shift 1 0 := by
  have := shift_subst_comm_gen e j 0 t
  simp [shift_zero] at this; exact this

/-! ## Substitution composition lemma (for the fundamental theorem)

The key infrastructure lemma: substituting with a "hole" environment
(bvar 0 :: γ.map shift) then filling the hole with `subst` is the same as
substituting with the filled environment (s :: γ).

Required by the fundamental theorem to connect the semantic lambda
(which uses subst for beta-reduction) with the open-term IH
(which uses substEnv for environment extension). -/

/-- The bvar case of the composition lemma: the entry at position k of
    liftEnvN c env_L, after applying subst c, equals the entry of liftEnvN c env_R.
    Proved by induction on c using shift_subst_comm. -/
private theorem liftEnvN_entry_subst (c : Nat) (γ : List Expr) (s : Expr) (k : Nat)
    (h : k < c + γ.length + 1) :
    (((liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0)))[k]?).getD default).subst c (s.shift c 0)
    = ((liftEnvN c (s :: γ))[k]?).getD default := by
  induction c generalizing k with
  | zero =>
    simp [liftEnvN]
    cases k with
    | zero => simp [List.getElem?_cons_zero, subst]
    | succ j =>
      simp [List.getElem?_cons_succ, List.getElem?_map]
      have hj : j < γ.length := by omega
      have hv := List.getElem?_eq_getElem (α := Expr) hj
      simp [hv, shift_subst_cancel]
  | succ c' ih =>
    simp [liftEnvN]
    cases k with
    | zero => simp [List.getElem?_cons_zero, subst]
    | succ j =>
      simp [List.getElem?_cons_succ, List.getElem?_map]
      have hj : j < c' + γ.length + 1 := by omega
      have hjL : j < (liftEnvN c' ((.bvar 0) :: γ.map (·.shift 1 0))).length := by
        rw [liftEnvN_length]; simp; omega
      have hjR : j < (liftEnvN c' (s :: γ)).length := by
        rw [liftEnvN_length]; simp; omega
      have hvL := List.getElem?_eq_getElem (α := Expr) hjL
      have hvR := List.getElem?_eq_getElem (α := Expr) hjR
      simp [hvL, hvR]
      rw [show shift (c' + 1) 0 s = (s.shift c' 0).shift 1 0 from (shift_succ s c').symm]
      rw [shift_subst_comm]
      congr 1
      have := ih j hj
      simp [hvL, hvR] at this
      exact this

/-- Generalized composition lemma, parameterized by binder depth c.
    At depth c, the environment has been lifted c times and the subst
    position is c with value s.shift c 0.

    The c=0 case gives the main composition lemma.

    PROOF STATUS: Fully proved (zero sorrys). Uses shift_subst_comm_gen via
    liftEnvN_entry_subst for the bvar case.
    The proof structure:
    - bvar: via liftEnvN_entry_subst (induction on c, uses shift_subst_comm)
    - lam/mu: IH on domain at depth c, IH on body at depth c+1
      (substEnv's lifting = liftEnvN (c+1), shift_succ converts the subst value)
    - app/asc: IH on both parts at depth c
    - type: trivial -/
theorem substEnv_subst_comp_gen (c : Nat) (e : Expr) (γ : List Expr) (s : Expr)
    (h : e.closedAt (c + γ.length + 1) = true)
    : (e.substEnv (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0)))).subst c (s.shift c 0)
    = e.substEnv (liftEnvN c (s :: γ)) := by
  induction e generalizing c with
  | type => rfl
  | bvar k =>
    simp [closedAt] at h
    unfold substEnv
    simp only [List.length_cons, List.length_map, liftEnvN_length]
    simp only [show c + (γ.length + 1) = c + γ.length + 1 from by omega, h, ite_true]
    exact liftEnvN_entry_subst c γ s k h
  | lam dom body ih_dom ih_body =>
    simp [closedAt, Bool.and_eq_true] at h
    obtain ⟨h_dom, h_body⟩ := h
    show Expr.lam
      ((dom.substEnv (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0)))).subst c (s.shift c 0))
      ((body.substEnv ((.bvar 0) :: (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0))).map (·.shift 1 0))).subst (c + 1) ((s.shift c 0).shift 1 0))
    = Expr.lam
      (dom.substEnv (liftEnvN c (s :: γ)))
      (body.substEnv ((.bvar 0) :: (liftEnvN c (s :: γ)).map (·.shift 1 0)))
    congr 1
    · exact ih_dom c h_dom
    · rw [show (.bvar 0 :: (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0))).map (·.shift 1 0))
            = liftEnvN (c + 1) ((.bvar 0) :: γ.map (·.shift 1 0)) from by simp [liftEnvN],
        show (.bvar 0 :: (liftEnvN c (s :: γ)).map (·.shift 1 0))
            = liftEnvN (c + 1) (s :: γ) from by simp [liftEnvN],
        shift_succ]
      exact ih_body (c + 1) (by rw [show c + 1 + γ.length + 1 = c + γ.length + 1 + 1 from by omega]; exact h_body)
  | app f a ih_f ih_a =>
    simp [closedAt, Bool.and_eq_true] at h
    show Expr.app
      ((f.substEnv (liftEnvN c _)).subst c (s.shift c 0))
      ((a.substEnv (liftEnvN c _)).subst c (s.shift c 0))
    = Expr.app (f.substEnv (liftEnvN c _)) (a.substEnv (liftEnvN c _))
    congr 1; exact ih_f c h.1; exact ih_a c h.2
  | asc t y ih_t ih_y =>
    simp [closedAt, Bool.and_eq_true] at h
    show Expr.asc
      ((t.substEnv (liftEnvN c _)).subst c (s.shift c 0))
      ((y.substEnv (liftEnvN c _)).subst c (s.shift c 0))
    = Expr.asc (t.substEnv (liftEnvN c _)) (y.substEnv (liftEnvN c _))
    congr 1; exact ih_t c h.1; exact ih_y c h.2
  | mu ann body ih_ann ih_body =>
    simp [closedAt, Bool.and_eq_true] at h
    obtain ⟨h_ann, h_body⟩ := h
    show Expr.mu
      ((ann.substEnv (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0)))).subst c (s.shift c 0))
      ((body.substEnv ((.bvar 0) :: (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0))).map (·.shift 1 0))).subst (c + 1) ((s.shift c 0).shift 1 0))
    = Expr.mu
      (ann.substEnv (liftEnvN c (s :: γ)))
      (body.substEnv ((.bvar 0) :: (liftEnvN c (s :: γ)).map (·.shift 1 0)))
    congr 1
    · exact ih_ann c h_ann
    · rw [show (.bvar 0 :: (liftEnvN c ((.bvar 0) :: γ.map (·.shift 1 0))).map (·.shift 1 0))
            = liftEnvN (c + 1) ((.bvar 0) :: γ.map (·.shift 1 0)) from by simp [liftEnvN],
        show (.bvar 0 :: (liftEnvN c (s :: γ)).map (·.shift 1 0))
            = liftEnvN (c + 1) (s :: γ) from by simp [liftEnvN],
        shift_succ]
      exact ih_body (c + 1) (by rw [show c + 1 + γ.length + 1 = c + γ.length + 1 + 1 from by omega]; exact h_body)

/-- Composition lemma at depth 0: the key lemma for the fundamental theorem.
    `(e.substEnv (bvar 0 :: γ.map shift)).subst 0 s = e.substEnv (s :: γ)`
    when e has at most γ.length + 1 free variables.

    This connects beta-reduction (subst 0) with environment extension (s :: γ). -/
theorem substEnv_subst_comp (e : Expr) (γ : List Expr) (s : Expr)
    (h : e.closedAt (γ.length + 1) = true)
    : (e.substEnv ((.bvar 0) :: γ.map (·.shift 1 0))).subst 0 s = e.substEnv (s :: γ) := by
  have := substEnv_subst_comp_gen 0 e γ s (by simpa using h)
  simpa [liftEnvN] using this

end Expr

