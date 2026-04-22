import Och.Syntax

/-!
# Normalization by Evaluation for Och

The eager-substitution `absEval` in `Eval.lean` copies the substituend
into every occurrence position, which makes `done_ ⊑ dNat` fan out
exponentially (iotaIntro substitutes `done_NF` for every `:self`
ascription in `dNat`'s body). NbE avoids this by evaluating into a
semantic domain with *closures*: substitution becomes environment
extension, so the substituend is shared, not copied.

This module replaced the substitution-based `absEval` (retired
2026-04-19); see DECISION-LOG.

References: Abel "NbE: Dependent Types and Impredicativity" (2013);
Christiansen "Checking Dependent Types with NbE: A Tutorial".
-/

namespace NbE

mutual
  /-- Semantic values. Closures capture the evaluation environment so
      substitution is delayed until the binder is opened. Neutrals use
      de Bruijn *levels* so they can be quoted back to indices without
      shifting. -/
  inductive Val where
    | type    : Val
    /-- Primitive bottom value. Self-evaluating (like `type`);
        non-applicable (no `vapp` arm). Corresponds to `Expr.bot`. -/
    | bot     : Val
    | lam     : Val → Closure → Val
    | iota    : Val → Closure → Val
    | «fix»   : Val → Closure → Val
    | neutral : Neutral → Val
    deriving Inhabited

  /-- Stuck computations. `var` is a de Bruijn *level*. `app` extends
      a neutral spine with a value argument. `stuckRec` represents a
      recursive head (fix/ι value) applied to a neutral argument —
      the eliminator can't fire on an abstract scrutinee. -/
  inductive Neutral where
    | var      : Nat → Neutral
    | app      : Neutral → Val → Neutral
    | stuckRec : Val → Val → Neutral
    deriving Inhabited

  structure Closure where
    body : Expr
    env  : List Val
    deriving Inhabited
end

abbrev Env := List Val

/-- The smallest `n` such that `closedAt n e` — i.e., one more
    than the maximum free bvar index in `e` (or `0` if closed).
    Used to trim closure environments to only the entries the
    body can actually reach, so `Closure.beq` doesn't miss on
    irrelevant env tails (e.g. two evaluations of the closed
    `dNat` term at different ambient envs). -/
def bvarBound : Expr → Nat
  | .bvar k => k + 1
  | .type => 0
  | .bot => 0
  | .lam dom body => max (bvarBound dom) (bvarBound body - 1)
  | .iota ann body | .fix ann body | .letE ann body =>
      max (bvarBound ann) (bvarBound body - 1)
  | .app f a => max (bvarBound f) (bvarBound a)
  | .asc t ty => max (bvarBound t) (bvarBound ty)

/-- Build a closure, trimming `env` to the prefix `body` can
    actually reach once opened. `bvar 0` in `body` is bound by
    the open itself; `bvar (k+1)` reaches `env[k]`. -/
def Closure.mk' (body : Expr) (env : Env) : Closure :=
  ⟨body, env.take (bvarBound body - 1)⟩

def Val.isNeutral : Val → Bool
  | .neutral _ => true
  | _ => false

/-- Default recursive-head unfold bound. Enough to compute through
    any small concrete dNat numeral (each `dsucc` layer costs one
    unfold for the fix and one for the resulting ι) while stopping
    the `(dsucc m)→Type` self-reference after one round. -/
def unfBound : Nat := 32

mutual
  /-- `unf` bounds the number of recursive-head (fix/ι) unfolds in
      the current application chain. Unlike absEval's `muSeen` it
      doesn't try syntactic cycle detection — closures share
      structure so the chain is linear, and a small bound suffices
      to compute through any concrete dNat numeral while stopping
      the `(dsucc m)→Type` self-reference in done_'s annotation. -/
  def eval (fuel unf : Nat) (env : Env) (e : Expr) : Option Val :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match e with
      | .type => some .type
      | .bot => some .bot
      | .bvar k => env[k]?
      | .lam dom body => do
          let dom' ← eval fuel unf env dom
          some (.lam dom' (.mk' body env))
      | .iota ann body => do
          let ann' ← eval fuel unf env ann
          some (.iota ann' (.mk' body env))
      | .fix ann body => do
          let ann' ← eval fuel unf env ann
          some (.fix ann' (.mk' body env))
      | .app f a => do
          let f' ← eval fuel unf env f
          let a' ← eval fuel unf env a
          vapp fuel unf f' a'
      | .letE v body => do
          let v' ← eval fuel unf env v
          eval fuel unf (v' :: env) body
      | .asc t _ty =>
          -- Ascription is computationally transparent: `(t : τ)`
          -- evaluates to `t` (matching `concEval` and
          -- `Subtype'.asc_L/R`). Previously evaluated `τ`, so
          -- `Nat_ ⊑ (zero_ : Nat_)` was accepted (= `Nat_ ⊑
          -- Nat_`); declaratively that's `Nat_ ⊑ zero_`, false.
          -- (SoundnessAudit A8.)
          eval fuel unf env t
  termination_by fuel

  def vapp (fuel unf : Nat) (f a : Val) : Option Val :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match f with
      | .lam _dom ⟨body, env⟩ =>
          eval fuel unf (a :: env) body
      | .iota _ann ⟨body, env⟩ =>
          if a.isNeutral || unf == 0 then
            some (.neutral (.stuckRec f a))
          else do
            let f' ← eval fuel (unf - 1) (f :: env) body
            vapp fuel (unf - 1) f' a
      | .fix _ann ⟨body, env⟩ =>
          if a.isNeutral || unf == 0 then
            some (.neutral (.stuckRec f a))
          else do
            let f' ← eval fuel (unf - 1) (f :: env) body
            vapp fuel (unf - 1) f' a
      | .neutral n => some (.neutral (.app n a))
      | .type => some (.neutral (.stuckRec f a))
      -- Bot is non-applicable (spec: Bot is a type; applying a value to it
      -- makes no sense). No arm for `.bot` above, so this branch is the
      -- exhaustiveness fallback, and `vapp .bot a = none` — stuck.
      -- See `docs/ideas/bottom.md`.
      | .bot => none
  termination_by fuel
end

/-!
## Fuel monotonicity for eval/vapp

If evaluation succeeds at fuel `n`, it succeeds with the same
result at any `m ≥ n`. The `unf` parameter is held fixed (it
threads through `eval` unchanged and only decrements inside a
single `vapp` chain, never across the `n ≤ m` bridge).

Equation lemmas for the `succ` case so the proof can step
through one fuel layer without whnf'ing the whole body.
-/

theorem eval_zero {unf ρ e} : eval 0 unf ρ e = none := by
  unfold eval; rfl
theorem vapp_zero {unf f a} : vapp 0 unf f a = none := by
  unfold vapp; rfl

theorem eval_vapp_fuel_mono :
    ∀ n,
    (∀ {m unf ρ e v}, n ≤ m →
        eval n unf ρ e = some v → eval m unf ρ e = some v) ∧
    (∀ {m unf f a v}, n ≤ m →
        vapp n unf f a = some v → vapp m unf f a = some v) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro _ _ _ _ _ _ h; rw [eval_zero] at h; cases h
    · intro _ _ _ _ _ _ h; rw [vapp_zero] at h; cases h
  | succ n ih =>
    obtain ⟨ihe, ihv⟩ := ih
    refine ⟨?_, ?_⟩
    -- eval (n+1) → eval m
    · intro m unf ρ e v hle h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
        ⟨m - 1, (Nat.succ_pred_eq_of_pos
                  (Nat.lt_of_lt_of_le n.succ_pos hle)).symm⟩
      have hle' : n ≤ m' := Nat.le_of_succ_le_succ hle
      unfold eval at h ⊢
      cases e with
      | type => exact h
      | bot => exact h
      | bvar => exact h
      | lam dom body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨dom', hdom, hv⟩ := h
          exact ⟨dom', ihe hle' hdom, hv⟩
      | iota ann body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨ann', hann, hv⟩ := h
          exact ⟨ann', ihe hle' hann, hv⟩
      | «fix» ann body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨ann', hann, hv⟩ := h
          exact ⟨ann', ihe hle' hann, hv⟩
      | app fn ar =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨f', hf, a', ha, hv⟩ := h
          exact ⟨f', ihe hle' hf, a', ihe hle' ha, ihv hle' hv⟩
      | letE val body =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨v', hv', hb⟩ := h
          exact ⟨v', ihe hle' hv', ihe hle' hb⟩
      | asc t ty => exact ihe hle' h
    -- vapp (n+1) → vapp m
    · intro m unf f a v hle h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
        ⟨m - 1, (Nat.succ_pred_eq_of_pos
                  (Nat.lt_of_lt_of_le n.succ_pos hle)).symm⟩
      have hle' : n ≤ m' := Nat.le_of_succ_le_succ hle
      unfold vapp at h ⊢
      cases f with
      | lam d cl =>
          obtain ⟨body, env⟩ := cl
          exact ihe hle' h
      | iota ann cl =>
          obtain ⟨body, env⟩ := cl
          dsimp only at h ⊢
          by_cases hc : (a.isNeutral || unf == 0) = true
          · simp only [hc, ↓reduceIte] at h ⊢; exact h
          · simp only [Bool.not_eq_true] at hc
            simp only [hc, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
            obtain ⟨f', hf, hv⟩ := h
            exact ⟨f', ihe hle' hf, ihv hle' hv⟩
      | «fix» ann cl =>
          obtain ⟨body, env⟩ := cl
          dsimp only at h ⊢
          by_cases hc : (a.isNeutral || unf == 0) = true
          · simp only [hc, ↓reduceIte] at h ⊢; exact h
          · simp only [Bool.not_eq_true] at hc
            simp only [hc, Bool.false_eq_true, ↓reduceIte,
                       Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
            obtain ⟨f', hf, hv⟩ := h
            exact ⟨f', ihe hle' hf, ihv hle' hv⟩
      | neutral => exact h
      | type => exact h
      | bot => exact h

theorem eval_fuel_mono {n m unf ρ e v}
    (hle : n ≤ m) (h : eval n unf ρ e = some v) :
    eval m unf ρ e = some v :=
  (eval_vapp_fuel_mono n).1 hle h

theorem vapp_fuel_mono {n m unf f a v}
    (hle : n ≤ m) (h : vapp n unf f a = some v) :
    vapp m unf f a = some v :=
  (eval_vapp_fuel_mono n).2 hle h

mutual
  /-- Read a value back to an expression. `depth` is the number of
      binders opened so far (= the next fresh de Bruijn level). -/
  def quote (fuel depth : Nat) (v : Val) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match v with
      | .type => some .type
      | .bot => some .bot
      | .neutral n => quoteNeutral fuel depth n
      | .lam dom cl => do
          let dom' ← quote fuel depth dom
          let body' ← quoteClosure fuel depth cl
          some (.lam dom' body')
      | .iota ann cl => do
          let ann' ← quote fuel depth ann
          let body' ← quoteClosure fuel depth cl
          some (.iota ann' body')
      | .fix ann cl => do
          let ann' ← quote fuel depth ann
          let body' ← quoteClosure fuel depth cl
          some (.fix ann' body')
  termination_by fuel

  def quoteClosure (fuel depth : Nat) (cl : Closure) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
      let bv := Val.neutral (.var depth)
      -- Opening a closure under a *neutral* fresh variable: any
      -- recursive-head application to that variable is stuck by
      -- the `a.isNeutral` gate, so the unfold bound here only
      -- matters for *closed* recursive applications captured in
      -- the environment. Use a small bound so the self-referential
      -- type annotations (e.g. `(dsucc m)→Type` in done_) terminate
      -- after one round.
      let v ← eval fuel 1 (bv :: cl.env) cl.body
      quote fuel (depth + 1) v
  termination_by fuel

  def quoteNeutral (fuel depth : Nat) (n : Neutral) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match n with
      | .var level =>
          if level < depth then some (.bvar (depth - 1 - level)) else none
      | .app n' v => do
          let f ← quoteNeutral fuel depth n'
          let a ← quote fuel depth v
          some (.app f a)
      | .stuckRec f a => do
          let f' ← quote fuel depth f
          let a' ← quote fuel depth a
          some (.app f' a')
  termination_by fuel
end

theorem quote_zero {depth v} : quote 0 depth v = none := by
  unfold quote; rfl
theorem quoteClosure_zero {depth cl} :
    quoteClosure 0 depth cl = none := by
  unfold quoteClosure; rfl
theorem quoteNeutral_zero {depth n} :
    quoteNeutral 0 depth n = none := by
  unfold quoteNeutral; rfl

/-- Fuel monotonicity for the `quote` family. Same combined-
induction pattern as `eval_vapp_fuel_mono`. -/
theorem quote_quoteClosure_quoteNeutral_fuel_mono :
    ∀ n,
    (∀ {m depth v e}, n ≤ m →
        quote n depth v = some e → quote m depth v = some e) ∧
    (∀ {m depth cl e}, n ≤ m →
        quoteClosure n depth cl = some e →
        quoteClosure m depth cl = some e) ∧
    (∀ {m depth ne e}, n ≤ m →
        quoteNeutral n depth ne = some e →
        quoteNeutral m depth ne = some e) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro _ _ _ _ _ h; rw [quote_zero] at h; cases h
    · intro _ _ _ _ _ h; rw [quoteClosure_zero] at h; cases h
    · intro _ _ _ _ _ h; rw [quoteNeutral_zero] at h; cases h
  | succ n ih =>
    obtain ⟨ihq, ihc, ihn⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- quote
    · intro m depth v e hle h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
        ⟨m - 1, (Nat.succ_pred_eq_of_pos
                  (Nat.lt_of_lt_of_le n.succ_pos hle)).symm⟩
      have hle' : n ≤ m' := Nat.le_of_succ_le_succ hle
      unfold quote at h ⊢
      cases v with
      | type => exact h
      | bot => exact h
      | neutral ne => exact ihn hle' h
      | lam dom cl =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨d', hd, b', hb, he⟩ := h
          exact ⟨d', ihq hle' hd, b', ihc hle' hb, he⟩
      | iota ann cl =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨a', ha, b', hb, he⟩ := h
          exact ⟨a', ihq hle' ha, b', ihc hle' hb, he⟩
      | «fix» ann cl =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨a', ha, b', hb, he⟩ := h
          exact ⟨a', ihq hle' ha, b', ihc hle' hb, he⟩
    -- quoteClosure
    · intro m depth cl e hle h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
        ⟨m - 1, (Nat.succ_pred_eq_of_pos
                  (Nat.lt_of_lt_of_le n.succ_pos hle)).symm⟩
      have hle' : n ≤ m' := Nat.le_of_succ_le_succ hle
      unfold quoteClosure at h ⊢
      simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
      obtain ⟨v, hev, hq⟩ := h
      exact ⟨v, eval_fuel_mono hle' hev, ihq hle' hq⟩
    -- quoteNeutral
    · intro m depth ne e hle h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 :=
        ⟨m - 1, (Nat.succ_pred_eq_of_pos
                  (Nat.lt_of_lt_of_le n.succ_pos hle)).symm⟩
      have hle' : n ≤ m' := Nat.le_of_succ_le_succ hle
      unfold quoteNeutral at h ⊢
      cases ne with
      | var => exact h
      | app n' v =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨f', hf, a', ha, he⟩ := h
          exact ⟨f', ihn hle' hf, a', ihq hle' ha, he⟩
      | stuckRec f a =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some] at h ⊢
          obtain ⟨f', hf, a', ha, he⟩ := h
          exact ⟨f', ihq hle' hf, a', ihq hle' ha, he⟩

theorem quote_fuel_mono {n m depth v e}
    (hle : n ≤ m) (h : quote n depth v = some e) :
    quote m depth v = some e :=
  (quote_quoteClosure_quoteNeutral_fuel_mono n).1 hle h

theorem quoteClosure_fuel_mono {n m depth cl e}
    (hle : n ≤ m) (h : quoteClosure n depth cl = some e) :
    quoteClosure m depth cl = some e :=
  (quote_quoteClosure_quoteNeutral_fuel_mono n).2.1 hle h

theorem quoteNeutral_fuel_mono {n m depth ne e}
    (hle : n ≤ m) (h : quoteNeutral n depth ne = some e) :
    quoteNeutral m depth ne = some e :=
  (quote_quoteClosure_quoteNeutral_fuel_mono n).2.2 hle h

/-- Normalize a closed expression. -/
def nf (fuel : Nat) (e : Expr) : Option Expr := do
  let v ← eval fuel unfBound [] e
  quote fuel 0 v

end NbE
