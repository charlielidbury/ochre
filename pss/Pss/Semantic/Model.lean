import Pss.Syntax
import Pss.Star
import Pss.Reduction
import Pss.Semantic.WeakHead
import Pss.Semantic.ParRed

/-!
# The model: graded extensions with inclusions

§3 of `pss/docs/03-revised-proof.md`: Definition 3.1 (`Mem`/`Match`/`Good`
— `s ∈ ⟦T⟧ₖ`, `MATCHₘ(v,w)`, `c ∈ ⟨a⟩ⱼ`), Definition 3.2 (semantic
judgements over closing substitutions), Lemma 3.3 (membership from
inclusion), and Theorem 5.1 (DS-TRANS is set-theoretic).

The three relations are defined by **mutual well-founded recursion** on
the lexicographic measure `(index, tag)` with `Match ↦ 0`, `Mem ↦ 1`,
`Good ↦ 2` (doc Def 3.1's well-foundedness remark): `Mem k` calls
`Match (k − j)` with `j < k` (tag `0 < 1` when `j = 0`, index drop
otherwise); `Match m` calls `Mem`/`Good` at `j′ < m`; `Good j` calls
`Mem` at `i ≤ j` (tag `1 < 2` at `i = j`). The inclusion components place
`Mem` in *negative* positions — fatal for an inductive, irrelevant for a
recursive definition. The proven unfolding lemmas `Mem_unfold` /
`Match_unfold` / `Good_unfold` are the load-bearing interface; nothing
downstream unfolds the definitions directly.

**Closedness policy (deliberate deviation from the doc, orchestrator-
approved).** The doc defines `⟦T⟧ₖ` on closed terms; here `Mem`, `Match`,
`Good` are defined on **all** terms with no closedness side conditions.
An open-headed term is weak-head normal and not a value, so (m1) already
excludes it from every `⟦T⟧ₖ` with `k ≥ 1`, and self-membership excludes
it from goodness — the model handles open terms gracefully. Closedness
is only genuinely needed in `Safety.lean`, where Fact 1.1 requires the
program closed.
-/

namespace Pss.Semantic

open Term (Value)

mutual

/-- **Definition 3.1** (doc §3): `Mem k s T` is `s ∈ ⟦T⟧ₖ`. For all
`j < k`, if `s ⇓ʲ v` then (m1) `v` is a value, (m2) `T ⇓ w` for some
value `w`, and (m3) `MATCH_{k−j}(v, w)`. `⟦T⟧₀` is everything;
divergence costs nothing. -/
def Mem (k : Nat) (s T : Term) : Prop :=
  ∀ j v, j < k → Converges j s v →
    Value v ∧ ∃ w, ConvergesTo T w ∧ Value w ∧ Match (k - j) v w
termination_by (k, 1)
decreasing_by
  simp_wf
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [Nat.sub_zero]
    exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- **Definition 3.1** (doc §3): `Match m v w` is `MATCHₘ(v, w)`, for
values. `w = Top` accepts everything; `w = λx≤a.b` demands `v = λx≤α.β`
with `α =β a` (bounds compared by raw conversion, doc remark (iii)) and,
for every tier `j′ < m` and good argument `c ∈ ⟨a⟩ⱼ′`, (t1) membership
`[c]β ∈ ⟦[c]b⟧ⱼ′` and (t2) the extension inclusion
`⟦[c]β⟧ⱼ′ ⊆ ⟦[c]b⟧ⱼ′` (doc remark (iv): inclusions make DS-TRANS
set-theoretic). `MATCH₀` imposes only the index-free shape clauses. -/
def Match (m : Nat) (v w : Term) : Prop :=
  w = .top ∨
  ∃ a b α β, w = .lam a b ∧ v = .lam α β ∧ Beta α a ∧
    ∀ j' c, j' < m → Good j' a c →
      Mem j' (β.subst1 c) (b.subst1 c) ∧
      ∀ s', Mem j' s' (β.subst1 c) → Mem j' s' (b.subst1 c)
termination_by (m, 0)
decreasing_by
  all_goals simp_wf
  all_goals exact Prod.Lex.left _ _ (by omega)

/-- **Definition 3.1** (doc §3): `Good j a c` is `c ∈ ⟨a⟩ⱼ` — the good
arguments of a bound at depth `j`: membership `c ∈ ⟦a⟧ⱼ`,
self-membership `c ∈ ⟦c⟧ⱼ`, and the downward-closed inclusions
`⟦c⟧ᵢ ⊆ ⟦a⟧ᵢ` for all `i ≤ j` (downward closure is **by fiat** — doc
remark (v): memberships are antitone automatically, inclusions are not). -/
def Good (j : Nat) (a c : Term) : Prop :=
  Mem j c a ∧ Mem j c c ∧ ∀ i s', i ≤ j → Mem i s' c → Mem i s' a
termination_by (j, 2)
decreasing_by
  · simp_wf
    exact Prod.Lex.right _ (by omega)
  · simp_wf
    exact Prod.Lex.right _ (by omega)
  · simp_wf
    rcases Nat.lt_or_ge i j with h | h
    · exact Prod.Lex.left _ _ h
    · have hij : i = j := Nat.le_antisymm ‹i ≤ j› h
      subst hij
      exact Prod.Lex.right _ (by omega)
  · simp_wf
    rcases Nat.lt_or_ge i j with h | h
    · exact Prod.Lex.left _ _ h
    · have hij : i = j := Nat.le_antisymm ‹i ≤ j› h
      subst hij
      exact Prod.Lex.right _ (by omega)

end

/-! ## The unfolding interface

Well-founded definitions do not reduce definitionally; these three
proven equivalences are the only way downstream files (and implementer
agents) consume Definition 3.1. -/

/-- Unfolding of `Mem` (Definition 3.1, member clause). -/
theorem Mem_unfold {k : Nat} {s T : Term} :
    Mem k s T ↔
      ∀ j v, j < k → Converges j s v →
        Value v ∧ ∃ w, ConvergesTo T w ∧ Value w ∧ Match (k - j) v w := by
  rw [Mem]

/-- Unfolding of `Match` (Definition 3.1, MATCH clause). -/
theorem Match_unfold {m : Nat} {v w : Term} :
    Match m v w ↔
      (w = .top ∨
       ∃ a b α β, w = .lam a b ∧ v = .lam α β ∧ Beta α a ∧
         ∀ j' c, j' < m → Good j' a c →
           Mem j' (β.subst1 c) (b.subst1 c) ∧
           ∀ s', Mem j' s' (β.subst1 c) → Mem j' s' (b.subst1 c)) := by
  rw [Match]

/-- Unfolding of `Good` (Definition 3.1, goodness clause). -/
theorem Good_unfold {j : Nat} {a c : Term} :
    Good j a c ↔
      Mem j c a ∧ Mem j c c ∧ ∀ i s', i ≤ j → Mem i s' c → Mem i s' a := by
  rw [Good]

/-! ## Semantic judgements (Definition 3.2)

De Bruijn form: closing substitutions are plain functions
`γ : Nat → Term`; `Ctx.Bound`'s shift discipline puts each bound in
scope of the whole context, so `t.subst γ` is the doc's `γtᵢ`. The
inclusion halves are carried **∀-indexed** (doc §4 discipline box:
inclusions are not antitone, so they are quantified over the index and
consumed at exactly the index of use). -/

/-- `γ ∈ ⟦Γ⟧ₖ` (Definition 3.2): each variable is a good argument of its
bound, under `γ`. -/
def SemCtx (k : Nat) (Γ : Ctx) (γ : Nat → Term) : Prop :=
  ∀ x t, Ctx.Bound Γ x t → Good k (t.subst γ) (γ x)

/-- `Γ ⊨ t ≤ u` (Definition 3.2): membership **and** extension
inclusion, at every index, under every good closing substitution. -/
def SemLe (Γ : Ctx) (t u : Term) : Prop :=
  ∀ k γ, SemCtx k Γ γ →
    Mem k (t.subst γ) (u.subst γ) ∧
    ∀ s, Mem k s (t.subst γ) → Mem k s (u.subst γ)

/-- `Γ ⊨ t wf` (Definition 3.2): self-membership (the inclusion half of
`Γ ⊨ t ≤ t` is reflexivity). -/
def SemWf (Γ : Ctx) (t : Term) : Prop :=
  ∀ k γ, SemCtx k Γ γ → Mem k (t.subst γ) (t.subst γ)

/-- `Γ ⊨ t ≡ u` (Definition 3.2): raw conversion plus well-formedness of
both endpoints. -/
def SemEq (Γ : Ctx) (t u : Term) : Prop :=
  Beta t u ∧ SemWf Γ t ∧ SemWf Γ u

/-- The semantic interpretation of the `⊲` metavariable (cf. `Pss.Rel`):
`≤ ↦ SemLe`, `≡ ↦ SemEq`. -/
def SemRel : Rel → Ctx → Term → Term → Prop
  | .le, Γ, t, u => SemLe Γ t u
  | .eq, Γ, t, u => SemEq Γ t u

/-- `Γ ⊨ t wf` is `Γ ⊨ t ≤ t` (Definition 3.2's remark). -/
theorem semWf_iff_semLe_self {Γ : Ctx} {t : Term} :
    SemWf Γ t ↔ SemLe Γ t t := by
  constructor
  · intro h k γ hγ
    exact ⟨h k γ hγ, fun s hs => hs⟩
  · intro h k γ hγ
    exact (h k γ hγ).1

/-- **Lemma 3.3 (membership from inclusion)**, the workhorse of the
fundamental theorem: every instrumented `≤`-rule carries wf of its left
endpoint, so per-rule obligations reduce to the inclusion half. -/
theorem semLe_of_inclusion {Γ : Ctx} {t u : Term} (hwf : SemWf Γ t)
    (hincl : ∀ k γ, SemCtx k Γ γ →
      ∀ s, Mem k s (t.subst γ) → Mem k s (u.subst γ)) :
    SemLe Γ t u :=
  fun k γ hγ => ⟨hincl k γ hγ _ (hwf k γ hγ), hincl k γ hγ⟩

/-- **Theorem 5.1 (DS-TRANS is free)**: membership composes through the
middle's inclusion, inclusions compose set-theoretically, all at one
fixed index. The middle term is never evaluated. -/
theorem SemLe.trans {Γ : Ctx} {s t u : Term}
    (h₁ : SemLe Γ s t) (h₂ : SemLe Γ t u) : SemLe Γ s u := by
  intro k γ hγ
  obtain ⟨m₁, i₁⟩ := h₁ k γ hγ
  obtain ⟨m₂, i₂⟩ := h₂ k γ hγ
  exact ⟨i₂ _ m₁, fun s' hs' => i₂ _ (i₁ _ hs')⟩

/-- `≡`-symmetry glue for the fundamental theorem's DS-SYM case. -/
theorem SemEq.symm {Γ : Ctx} {t u : Term} (h : SemEq Γ t u) :
    SemEq Γ u t :=
  ⟨Beta.symm h.1, h.2.2, h.2.1⟩

/-- `≡`-transitivity glue for the fundamental theorem's DS-TRANS ≡-case. -/
theorem SemEq.trans {Γ : Ctx} {t u v : Term}
    (h₁ : SemEq Γ t u) (h₂ : SemEq Γ u v) : SemEq Γ t v :=
  ⟨Beta.trans h₁.1 h₂.1, h₁.2.1, h₂.2.2⟩

/-! ## The γ-kit

σ-calculus equations relating context extension `γ[x↦c]`
(= `Term.scons c γ`) to the substitution library of `Pss.Syntax`
(doc §9: "expect a small lemma kit relating `subst`, closedness, and
`γ[x↦c]`"). `t.subst Term.var = t` is `Term.subst_var`. -/

/-- A shifted term ignores the head of an extended substitution:
`(↑t)[γ[x↦c]] = t[γ]`. Closes the `here` case of `SemCtx.cons`. -/
theorem shift_subst_scons (t c : Term) (γ : Nat → Term) :
    (t.shift 1).subst (Term.scons c γ) = t.subst γ := by
  show (t.rename (· + 1)).subst (Term.scons c γ) = t.subst γ
  rw [Term.subst_rename]
  rfl

/-- Lifting-then-instantiating is extension:
`(u[⇑γ])[x↦c] = u[γ[x↦c]]`. The equation that makes `W-FUN`'s tier
descent and the β-contractum line up with `Term.scons c γ`. -/
theorem subst_liftSubst_subst1 (u c : Term) (γ : Nat → Term) :
    (u.subst (Term.liftSubst γ)).subst1 c = u.subst (Term.scons c γ) := by
  show (u.subst (Term.liftSubst γ)).subst (Term.scons c Term.var)
      = u.subst (Term.scons c γ)
  rw [Term.subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => exact Term.shift_subst1 (γ n) c

/-- Extending a good substitution by a good argument (doc §6, W-FUN
case: "the new entry is literally the tier's domain condition"). -/
theorem SemCtx.cons {k : Nat} {Γ : Ctx} {γ : Nat → Term} {t c : Term}
    (hγ : SemCtx k Γ γ) (hc : Good k (t.subst γ) c) :
    SemCtx k (t :: Γ) (Term.scons c γ) := by
  intro x s hbound
  cases hbound with
  | here =>
    rw [shift_subst_scons]
    exact hc
  | there h =>
    rw [shift_subst_scons]
    exact hγ _ _ h

/-- Every substitution closes the empty context (consumed by §7: the
fundamental theorem at `Γ = ∅` instantiates with `γ = Term.var`). -/
theorem semCtx_nil {k : Nat} {γ : Nat → Term} : SemCtx k [] γ :=
  fun _ _ h => nomatch h

end Pss.Semantic
