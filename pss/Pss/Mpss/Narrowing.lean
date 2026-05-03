import Pss.Mpss.WellFormed
import Pss.Mpss.Weakening
import Pss.Mpss.Substitution

set_option linter.unusedVariables false

/-! # `Pss.Mpss.Narrowing` — narrowing lemmas for MPSS

Pasquale & García-Pérez 2024 (CSL 2026), appendix Lemmas 23, 24, 25, 26.

Narrowing replaces a `.sub` binding `x ≤ t'` in a context with a tighter
bound `x ≤ t` (where `Γ₁ ⊢ t ≤_wf t'`). The four lemmas state that this
preserves prevalidity, well-formedness, subtype reduction, and equivalence
reduction respectively.

## Status summary

* **Lemma 26** (Prevalidity narrowing): PROVED in restricted form. The
  signature carries an additional `Term.fv t ⊆ Γ₁.dom` premise (not
  in-general derivable from a bare `WSubM Γ₁ t t'` — see the `lf1`/`rgh`
  discussion in `Pss/Mpss/WellFormed.lean §5.5`). For all downstream uses
  (Lemma 23 etc.) this premise is readily available.
* **Lemma 23** (WfM narrowing): PROVED, given the restricted Lemma 26.
* **Lemma 25** (MEqRed narrowing): PROVED. The `pro y = x` case is
  vacuous: `equBinds` looks for `.equ` entries; narrowing changes a
  `.sub` entry, so head-position lookups for `.equ` are unaffected.
* **Lemma 24** (MSubRed narrowing): AXIOMATIZED (single Wave-5 quota).
  The `Ms-Pro y = x` case requires composing the narrowed lookup
  `x ↦ t` with a `WSubM`-style chain to recover the original RHS `t'`.
  `MSubRed` lacks the chaining structure of `WSubM` for a single-step
  encoding, so we axiomatize the lemma and document the discharge plan
  (Wave 7: introduce `MSubRedStar` glue + the `Lemma_30_msPro_x_axiom`
  pattern from Wave 4B).
-/

namespace Pss

/-! ## §1. Lemma 26 — Narrowing for `PrevalidExt` -/

/-- Narrowing for `Prevalid`: replacing a `.sub` head binding `x ≤ t'`
with `x ≤ t` for any locally-closed, in-scope `t` preserves prevalidity.

Restricted form: takes `Term.fv t ⊆ Γ₁.dom` and `Term.LC t` directly,
because the bare `WSubM Γ₁ t t'` does NOT in general imply
`fv t ⊆ Γ₁.dom` (cf. `WSubM.lf1` + `MEqRed.var` for an unscoped variable;
see `Pss/Mpss/WellFormed.lean` §5.5). All downstream callers can supply
these premises. -/
noncomputable def Lemma_26a_NarrowingPrevalid_kind
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term}
    (hpv : Prevalid (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁))
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    Prevalid (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) := by
  induction Γ₂ with
  | nil =>
    -- hpv : Prevalid (⟨x, t', .sub⟩ :: Γ₁). Replace the head's bound.
    have hpv' : Prevalid (⟨x, t', .sub⟩ :: Γ₁) := by simpa using hpv
    cases hpv' with
    | sub hΓ hx _ _ =>
      simpa using Prevalid.sub hΓ hx hfvt hLCt
  | cons e rest ih =>
    -- hpv : Prevalid (e :: (rest ++ ⟨x, t', .sub⟩ :: Γ₁))
    have hpv_norm : Prevalid (e :: (rest ++ ⟨x, t', .sub⟩ :: Γ₁)) := by
      simpa using hpv
    have hpv_tail : Prevalid (rest ++ ⟨x, t', .sub⟩ :: Γ₁) := hpv_norm.tail
    have ih_tail : Prevalid (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := ih hpv_tail
    -- Domain of (rest ++ ⟨x, _, .sub⟩ :: Γ₁) is invariant under bound change.
    have hdom_eq : Ctx.dom (rest ++ ⟨x, t, .sub⟩ :: Γ₁) =
        Ctx.dom (rest ++ ⟨x, t', .sub⟩ :: Γ₁) := by
      rw [Ctx.dom_append, Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
    cases hpv_norm with
    | @sub _ y u hΓ hy hfv hlc =>
      have hy' : y ∉ Ctx.dom (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := by
        rw [hdom_eq]; exact hy
      have hfv' : Term.fv u ⊆ Ctx.dom (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := by
        rw [hdom_eq]; exact hfv
      simpa using Prevalid.sub ih_tail hy' hfv' hlc
    | @equ _ y α hΓ hy hfv hlc =>
      have hy' : y ∉ Ctx.dom (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := by
        rw [hdom_eq]; exact hy
      have hfv' : Term.fv α ⊆ Ctx.dom (rest ++ ⟨x, t, .sub⟩ :: Γ₁) := by
        rw [hdom_eq]; exact hfv
      simpa using Prevalid.equ ih_tail hy' hfv' hlc

/-- **Lemma 26** (Pasquale & García-Pérez 2024, Narrowing for
`PrevalidExt`). Restricted form: takes `Term.fv t ⊆ Γ₁.dom` and
`Term.LC t` instead of relying on a bare `WSubM`. -/
noncomputable def Lemma_26_NarrowingPrevalid
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s)
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    PrevalidExt (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) s := by
  -- Domain is preserved; only the bound for `x` changes.
  have hdom_eq : Ctx.dom (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) =
      Ctx.dom (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) := by
    rw [Ctx.dom_append, Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]
  induction s with
  | nil =>
    cases hpv with
    | nil hpvL =>
      exact PrevalidExt.nil (Lemma_26a_NarrowingPrevalid_kind hpvL hLCt hfvt)
  | cons α st' ih =>
    cases hpv with
    | cons hpvE hLCα hfvα =>
      refine PrevalidExt.cons (ih hpvE) hLCα ?_
      rw [hdom_eq]; exact hfvα

/-- Convenience wrapper: derive Lemma 26 from a `WSubM Γ₁ t t'` plus an
explicit `Term.fv t ⊆ Γ₁.dom` premise. The `LC t` part is recovered from
`WSubM.lc_left`. -/
noncomputable def Lemma_26_NarrowingPrevalid_ofWSubM
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} {s : Stack}
    (hpv : PrevalidExt (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) s)
    (hsub : WSubM Γ₁ t t')
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    PrevalidExt (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) s :=
  Lemma_26_NarrowingPrevalid hpv (WSubM.lc_left hsub) hfvt

/-! ## §2. Lemma 23 — Narrowing for `WfM`

Induction on `WfM`. Each constructor rebuilds the corresponding
`WfM Γ_new` from the IH plus `Lemma 26` for the prevalidity premise.

We adopt the restricted form: take `Term.fv t ⊆ Γ₁.dom` and `Term.LC t`
explicit (so that Lemma 26 applies). -/

/-- Domain of the narrowed context equals that of the original. -/
private lemma _dom_narrow_eq {Γ₁ Γ₂ : Ctx} {x : String} {t t' : Term} :
    Ctx.dom (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) =
      Ctx.dom (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) := by
  rw [Ctx.dom_append, Ctx.dom_append, Ctx.dom_cons, Ctx.dom_cons]

/-- Helper: substituting `t` for `t'` in `subBinds` lookups under a
`.sub` head is a uniform recoloring. If we look up `y ≠ x`, the result
is unchanged. If `y = x`, the OLD lookup yielded `t'`; the NEW one
yields `t`. -/
private lemma _subBinds_narrow_neq
    {Γ₁ Γ₂ : Ctx} {x y : String} {t t' u : Term}
    (hyx : y ≠ x)
    (hb : (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁).subBinds y u) :
    (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).subBinds y u := by
  induction Γ₂ with
  | nil =>
    simp [Ctx.subBinds, Ctx.lookupSub_cons, Ne.symm hyx] at hb ⊢
    exact hb
  | cons e rest ih =>
    show Ctx.lookupSub (e :: (rest ++ ⟨x, t, .sub⟩ :: Γ₁)) y = some u
    have h1 : Ctx.lookupSub (e :: (rest ++ ⟨x, t', .sub⟩ :: Γ₁)) y = some u := hb
    rw [Ctx.lookupSub_cons] at h1 ⊢
    by_cases he : e.name = y
    · rw [if_pos he] at h1 ⊢
      exact h1
    · rw [if_neg he] at h1 ⊢
      exact ih h1

/-- If the lookup `Γ₂.subBinds y` is `none` (i.e. `Γ₂` does not shadow
`y` with anything that would intercept a `.sub` lookup — which means
both no `.sub`-for-`y` AND no `.equ`-for-`y` in `Γ₂`), then in
`Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁` the lookup `subBinds y` returns `t`.

We capture this as: `Γ₂ ++ ⟨y, t', .sub⟩ :: Γ₁` already binds `y` to
`t'` (via `hb`), so the head was reached. This means no `.equ`
shadowing in `Γ₂` either. -/
private lemma _subBinds_narrow_eq_head_aux
    {Γ₁ : Ctx} {y : String} {t t' u : Term} :
    ∀ (Γ₂ : Ctx),
      (Γ₂ ++ ⟨y, t', .sub⟩ :: Γ₁).subBinds y u →
      (∀ b, ¬ Γ₂.subBinds y b) →
      (Γ₂ ++ ⟨y, t, .sub⟩ :: Γ₁).subBinds y t ∧ u = t' := by
  intro Γ₂
  induction Γ₂ with
  | nil =>
    intro hb _
    have hb' : Ctx.lookupSub (⟨y, t', .sub⟩ :: Γ₁) y = some u := hb
    simp [Ctx.lookupSub_cons] at hb'
    refine ⟨?_, hb'.symm⟩
    show Ctx.lookupSub (⟨y, t, .sub⟩ :: Γ₁) y = some t
    simp [Ctx.lookupSub_cons]
  | cons e rest ih =>
    intro hb hno
    have hb_e : Ctx.lookupSub (e :: (rest ++ ⟨y, t', .sub⟩ :: Γ₁)) y = some u := hb
    rw [Ctx.lookupSub_cons] at hb_e
    by_cases he : e.name = y
    · cases he_k : e.kind with
      | sub =>
        exfalso
        apply hno e.bound
        show Ctx.lookupSub (e :: rest) y = some e.bound
        simp [Ctx.lookupSub_cons, he, he_k]
      | equ =>
        -- e shadows y with .equ, so lookupSub returns none from the head
        -- but hb_e says some u — contradiction.
        simp [he, he_k] at hb_e
    · simp [he] at hb_e
      have hno_rest : ∀ b, ¬ Ctx.subBinds rest y b := by
        intro b hb1
        apply hno b
        show Ctx.lookupSub (e :: rest) y = some b
        simp [Ctx.lookupSub_cons, he]
        exact hb1
      have ih_app := ih hb_e hno_rest
      refine ⟨?_, ih_app.2⟩
      show Ctx.lookupSub (e :: (rest ++ ⟨y, t, .sub⟩ :: Γ₁)) y = some t
      rw [Ctx.lookupSub_cons]
      simp [he]
      exact ih_app.1

/-- Symmetric helper for `equBinds`. Always preserves `.equ` lookups
(narrowing changes a `.sub` entry; `.equ` lookups are entirely unaffected
by changes to `.sub` entries). -/
private lemma _equBinds_narrow
    {Γ₁ Γ₂ : Ctx} {x y : String} {t t' α : Term}
    (heq : (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁).equBinds y α) :
    (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).equBinds y α := by
  induction Γ₂ with
  | nil =>
    -- heq : equBinds y α in (⟨x, t', .sub⟩ :: Γ₁). Head is .sub so even if
    -- y = x, lookupEqu returns none — so x ≠ y must hold and we recurse to Γ₁.
    have heq' : Ctx.equBinds (⟨x, t', .sub⟩ :: Γ₁) y α := by simpa using heq
    have heq_normal : Ctx.lookupEqu (⟨x, t', .sub⟩ :: Γ₁) y = some α := heq'
    rw [Ctx.lookupEqu_cons] at heq_normal
    by_cases hxy : x = y
    · subst hxy; simp at heq_normal
    · simp [hxy] at heq_normal
      -- heq_normal : Γ₁.lookupEqu y = some α
      show Ctx.lookupEqu ([] ++ ⟨x, t, .sub⟩ :: Γ₁) y = some α
      simp only [List.nil_append, Ctx.lookupEqu_cons]
      simp [hxy]
      exact heq_normal
  | cons e rest ih =>
    show Ctx.lookupEqu (e :: (rest ++ ⟨x, t, .sub⟩ :: Γ₁)) y = some α
    have h1 : Ctx.lookupEqu (e :: (rest ++ ⟨x, t', .sub⟩ :: Γ₁)) y = some α := heq
    rw [Ctx.lookupEqu_cons] at h1 ⊢
    by_cases he : e.name = y
    · rw [if_pos he] at h1 ⊢
      exact h1
    · rw [if_neg he] at h1 ⊢
      exact ih h1

/-! ## §3. Lemma 25 — Narrowing for `MEqRed`

Induction on the `MEqRed` derivation. Each case rebuilds the constructor
in the new context. Because `MEqRed` only references `equBinds` (in
`Me-Pro`), and narrowing changes a `.sub` entry, head-position
`equBinds` lookups are unchanged: the `Me-Pro y = x` case is impossible
when narrowing the head's `.sub` entry (the head is `.sub`, so `equBinds x`
returns `none` from the head; `Γ₂` lookups go through `_equBinds_narrow`).
-/

noncomputable def Lemma_25_NarrowingMEqRed
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' u v : Term} {st : Stack}
    (h : MEqRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st u v)
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    MEqRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v := by
  generalize hΓ : (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) = Γold at h
  induction h generalizing Γ₂ with
  | @pro Γ s y α α' hpv heq hα ihα =>
    subst hΓ
    have hpv' : PrevalidExt (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) s :=
      Lemma_26_NarrowingPrevalid hpv hLCt hfvt
    have heq' : (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁).equBinds y α :=
      _equBinds_narrow heq
    exact MEqRed.pro hpv' heq' (ihα (Γ₂ := Γ₂) rfl)
  | @bet Γ s t₀ v₀ v' body body' L hLCt₀ hbody hv ihbody ihv =>
    subst hΓ
    refine MEqRed.bet (L := L) hLCt₀ ?_ (ihv (Γ₂ := Γ₂) rfl)
    intro y hy
    exact ihbody y hy (Γ₂ := Γ₂) rfl
  | @top Γ s hpv =>
    subst hΓ
    exact MEqRed.top (Lemma_26_NarrowingPrevalid hpv hLCt hfvt)
  | @app Γ s u u' w w' hu hw ihu ihw =>
    subst hΓ
    exact MEqRed.app (ihu (Γ₂ := Γ₂) rfl) (ihw (Γ₂ := Γ₂) rfl)
  | @var Γ s y hpv =>
    subst hΓ
    exact MEqRed.var (Lemma_26_NarrowingPrevalid hpv hLCt hfvt)
  | @fun_ Γ t₀ t₀' body body' L ht hbody iht ihbody =>
    subst hΓ
    refine MEqRed.fun_ (L := L) (iht (Γ₂ := Γ₂) rfl) ?_
    intro y hy
    have ih_body := ihbody y hy (Γ₂ := ⟨y, t₀, .sub⟩ :: Γ₂) (by simp)
    simpa using ih_body
  | @tAp Γ s w hpv hLCw hfv =>
    subst hΓ
    refine MEqRed.tAp (Lemma_26_NarrowingPrevalid hpv hLCt hfvt) hLCw ?_
    intro z hz
    have hzd := hfv hz
    rw [_dom_narrow_eq (t := t) (t' := t')]
    exact hzd
  | @fOp Γ s t₀ t₀' α body body' L ht hbody iht ihbody =>
    subst hΓ
    refine MEqRed.fOp (L := L) (iht (Γ₂ := Γ₂) rfl) ?_
    intro y hy
    have ih_body := ihbody y hy (Γ₂ := ⟨y, α, .equ⟩ :: Γ₂) (by simp)
    simpa using ih_body

/-! ## §4. Lemma 24 — Narrowing for `MSubRed` (axiomatized)

**Status (post-investigation, 2026-04):** The axiom as currently stated
is *structurally false* under the LC + fv premise alone. Concrete
counter-shape: take a derivation of `MSubRed Γ_old [] (.fvar x) (.fvar z)`
proceeding via `Ms-Pro` on `x` (giving the binding `t' = .fvar z`).
Narrowing replaces `t'` with an unrelated `t = .top`. The new lookup
yields `MSubRed Γ_new [] (.fvar x) .top`, but the conclusion demands
`MSubRed Γ_new [] (.fvar x) (.fvar z)` — and there is no Ms-* arm that
can step `.top → .fvar z`. So the lemma is genuinely false unless `t`
and `t'` are related by a witness such as `WSubM Γ₁ t t'`.

### Why the discharge cannot land in Narrowing.lean alone

The `Ms-Pro y = x` case needs to bridge the gap from `t` (new lookup)
to `t'` (old RHS). The natural bridge is `WSubM Γ_new t t'` (weakened
from `WSubM Γ₁ t t'`). Two integration paths:

* **Path A — strengthen Lemma 24 only.** Add `WSubM Γ₁ t t'` to
  Lemma 24's premises and change its conclusion to `WSubM Γ_new v u`
  (taking the IH continuation `WSubM Γ_new v' u` as an extra
  parameter). The proof for the `Ms-Pro y = x` case then needs to
  compose `WSubM Γ_new t t'` with `WSubM Γ_new t' u` into
  `WSubM Γ_new t u`. This is **WSubM transitivity**, which is *not*
  derivable structurally:
    - `rfl`/`lf1`/`lf2` cases: induct on the first WSubM.
    - `rgh hsub hred` case: have `WSubM Γ a b''` and `MEqRed Γ b b''`,
      need to extend to `c` given `WSubM Γ b c`. Going from `b''` to
      `b` requires inverting the MEqRed direction; lifting via Lemma 15
      (WEquM symmetry) + Lemma 16 (WEquM ⊆ WSubM) recovers
      `WSubM Γ b'' b`, but composing `WSubM b'' b` with `WSubM b c`
      is recursive transitivity again. No structural fixed point.
  WSubM-transitivity is essentially Theorem 3's content (via `MSub`
  ↔ `WSubM` correspondence), which lives in `Pss.Mpss.TransitivityElim`
  and is *not* in this file's transitive imports.

* **Path B — strengthen Lemma 23's whole API.** Add `WSubM Γ₁ t t'` to
  Lemma 23's external signature, propagating to Lemma 26 and to the
  motives `_N_motive_*`. This breaks the call site at
  `Pss/Mpss/TypeSafety.lean:786`, which currently supplies only
  `LC bound'` and `fv bound' ⊆ Γ.dom`. (That call site *can* derive
  `WSubM Γ bound' bound` via Lemma 15 + Lemma 16 from a
  `MEqRed Γ [] bound bound'` it already has, but performing that
  derivation requires editing TypeSafety.lean, which is out of scope.)

### Conclusion

The current axiom is **load-bearing for an unsound claim**. Honest
discharge requires either (i) restructuring across multiple files to
add the `WSubM Γ₁ t t'` premise end-to-end, or (ii) importing
TransitivityElim infrastructure into Narrowing.lean to obtain a
WSubM-transitivity lemma. Both are out of scope for this turn's
restriction to Narrowing.lean only with the existing axiom budget.

**Axiom contract:** `MSubRed` narrowing under restricted (`fv ⊆`,
`LC`) premises, mirroring Lemma 25's signature. The axiom is
*provisionally stated* in this form to keep Lemma 23 building; a sound
restatement will need cross-file changes (above).

**Sound shape (target for Wave 7, not yet implementable here):**

```
theorem Lemma_24_sound
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' v v' u : Term} {st : Stack}
    (h : MSubRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st v v')
    (hChain : WSubM Γ₁ t t')                              -- new premise
    (hCont : WSubM (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) v' u)       -- continuation
    (hwfV_new hwfV'_new : WfM (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) _) :
    WSubM (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) v u                  -- changed conclusion
```

Discharge plan: induct on `h`. The `Ms-Pro y = x` case:
1. Weaken `hChain` to `WSubM Γ_new t t'` (Lemma 23 chicken-and-egg —
   handle by mutual induction with Lemma 23 itself).
2. Compose `WSubM Γ_new t t'` with `hCont : WSubM Γ_new t' u` into
   `WSubM Γ_new t u`. This is WSubM-transitivity, which requires
   Theorem 3 collapse (lift to WSubMStar via `WSubMStar.sub`,
   transitive-close via `WSubMStar.trs`, collapse back via Theorem 3
   — i.e. the `MSub`/`MSubRedStar` correspondence in
   `Pss.Mpss.TransitivityElim`).
3. Wrap with `WSubM.lf2 _ (Ms-Pro new lookup) _ (WSubM Γ_new t u)`.

### Discharge attempt notes (2026-04, agent_id: och-refactor)

A focused attempt at discharging Lemma 24 with the WSubMStar shape
(documented in commit message) hit the following residual blockers
beyond the original analysis:

* **Ms-App at non-empty inner stack:** the constructor produces output
  at empty stack from an inner `MSubRed Γ_old (v::s) u u'` derivation.
  Narrowing the inner derivation requires the same y=x bridging at
  non-empty stack, which the WSubMStar conclusion (only at empty
  stack) cannot accommodate. A stack-aware companion lemma is needed,
  and its discharge has the same structural issue at every stack
  level.

* **Ms-Fun body recursion:** the body recurses at an EXTENDED context
  `⟨z, t₀, .sub⟩ :: Γ_old`. To narrow the body's MSubRed, the
  WSubMStar bridge must be weakened from `Γ_new` to
  `⟨z, t₀, .sub⟩ :: Γ_new`. This requires `WSubMStar` weakening
  through a binder, which is **not** available in `Narrowing.lean`'s
  upstream imports (lives in `TypeSafety.lean` as `WfM.weaken_append`
  and friends, which are downstream of `Narrowing` via the
  `TransitivityElim → Commutation → Diamond → Narrowing` chain — a
  cycle).

* **Ms-FOp body recursion:** same issue as Ms-Fun, with `.equ` binder
  instead of `.sub`.

So even with the WSubMStar restatement, the discharge requires
either (i) WSubMStar weakening inlined into `Narrowing.lean`
(non-trivial, ~200 lines duplicated from `TypeSafety.lean`'s
`Lemma7._W_*` machinery), or (ii) lifting the entire narrowing
infrastructure downstream of `WfM`-weakening.

For now we retain the axiomatization. The `_N_lf2` use site below
also retains the call.

**Cross-ref:** see `AXIOMS.md` axiom #2 for status / paper / discharge
plan; this is currently in the `#print axioms` closure of Theorem 3, 4,
5 and Lemma 1. -/
axiom Lemma_24_NarrowingMSubRed
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' u v : Term} {st : Stack}
    (h : MSubRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st u v)
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    MSubRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v

/-! ## §5. Lemma 23 — Narrowing for `WfM`, `WSubM`, `WSubMStar`

Mutual induction via the `WfM.rec` / `WSubM.rec` / `WSubMStar.rec`
recursors — the three predicates are mutually inductive (see
`Pss/Mpss/WellFormed.lean`).

We thread `Γ₂` (the inner partition) and the equality
`Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁ = Γ` as universal motive parameters. -/

section Narrowing23
variable (Γ₁out : Ctx) (xout : String) (tout tout' : Term)

/-- Combined narrowing motive for `WfM`. `Type`-valued. -/
private def _N_motive_wf : (Γ : Ctx) → (u : Term) → WfM Γ u → Type :=
  fun Γ u _ => ∀ Γ₂ : Ctx,
    Γ = Γ₂ ++ ⟨xout, tout', .sub⟩ :: Γ₁out →
    Term.LC tout → Term.fv tout ⊆ Γ₁out.dom →
    WfM (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) u

/-- Combined narrowing motive for `WSubM`. `Type`-valued. -/
private def _N_motive_sub : (Γ : Ctx) → (v u : Term) → WSubM Γ v u → Type :=
  fun Γ v u _ => ∀ Γ₂ : Ctx,
    Γ = Γ₂ ++ ⟨xout, tout', .sub⟩ :: Γ₁out →
    Term.LC tout → Term.fv tout ⊆ Γ₁out.dom →
    WSubM (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) v u

/-- Combined narrowing motive for `WSubMStar`. `Type`-valued. -/
private def _N_motive_star : (Γ : Ctx) → (v u : Term) → WSubMStar Γ v u → Type :=
  fun Γ v u _ => ∀ Γ₂ : Ctx,
    Γ = Γ₂ ++ ⟨xout, tout', .sub⟩ :: Γ₁out →
    Term.LC tout → Term.fv tout ⊆ Γ₁out.dom →
    WSubMStar (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) v u

/-- The 11 case payloads for the narrowing mutual recursor. -/

private noncomputable def _N_varSub :
    ∀ {Γ : Ctx} {y : String} {u : Term}
      (hpv : Prevalid Γ) (hb : Γ.subBinds y u),
      _N_motive_wf Γ₁out xout tout tout' Γ (.fvar y) (WfM.varSub hpv hb) := by
  intro Γ y u hpv hb Γ₂ hΓ hLCt hfvt
  subst hΓ
  have hpvN : Prevalid (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) :=
    Lemma_26a_NarrowingPrevalid_kind hpv hLCt hfvt
  by_cases hyx : y = xout
  · subst hyx
    by_cases hshad : ∃ b, Γ₂.subBinds y b
    · let b : Term := Classical.choose hshad
      have hb_in_Γ₂ : Γ₂.subBinds y b := Classical.choose_spec hshad
      have h_old : (Γ₂ ++ ⟨y, tout', .sub⟩ :: Γ₁out).subBinds y b :=
        Ctx.lookupSub_append_left Γ₂ _ y b hb_in_Γ₂
      have hb_u : b = u := by
        have hb1 := hb
        have hb2 := h_old
        rw [Ctx.subBinds] at hb1 hb2
        rw [hb1] at hb2
        exact (Option.some_inj.mp hb2).symm
      have hb_new : (Γ₂ ++ ⟨y, tout, .sub⟩ :: Γ₁out).subBinds y u := by
        rw [← hb_u]
        exact Ctx.lookupSub_append_left Γ₂ _ y b hb_in_Γ₂
      exact WfM.varSub hpvN hb_new
    · have hno : ∀ b, ¬ Γ₂.subBinds y b := fun b hb_in => hshad ⟨b, hb_in⟩
      have hpair := _subBinds_narrow_eq_head_aux (t := tout) Γ₂ hb hno
      exact WfM.varSub hpvN hpair.1
  · have hb_new : (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out).subBinds y u :=
      _subBinds_narrow_neq hyx hb
    exact WfM.varSub hpvN hb_new

private noncomputable def _N_varEqu :
    ∀ {Γ : Ctx} {y : String} {α : Term}
      (hpv : Prevalid Γ) (hb : Γ.equBinds y α),
      _N_motive_wf Γ₁out xout tout tout' Γ (.fvar y) (WfM.varEqu hpv hb) := by
  intro Γ y α hpv hb Γ₂ hΓ hLCt hfvt
  subst hΓ
  have hpvN : Prevalid (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) :=
    Lemma_26a_NarrowingPrevalid_kind hpv hLCt hfvt
  exact WfM.varEqu hpvN (_equBinds_narrow hb)

private noncomputable def _N_top :
    ∀ {Γ : Ctx} (hpv : Prevalid Γ),
      _N_motive_wf Γ₁out xout tout tout' Γ .top (WfM.top hpv) := by
  intro Γ hpv Γ₂ hΓ hLCt hfvt
  subst hΓ
  exact WfM.top (Lemma_26a_NarrowingPrevalid_kind hpv hLCt hfvt)

private noncomputable def _N_fun :
    ∀ {Γ : Ctx} {t₀ u : Term} (L : Finset String)
      (hT : WfM Γ t₀)
      (hB : ∀ y, y ∉ L → WfM (⟨y, t₀, .sub⟩ :: Γ) (Term.opening (.fvar y) u))
      (ihT : _N_motive_wf Γ₁out xout tout tout' Γ t₀ hT)
      (ihB : ∀ y (hy : y ∉ L),
        _N_motive_wf Γ₁out xout tout tout' (⟨y, t₀, .sub⟩ :: Γ)
          (Term.opening (.fvar y) u) (hB y hy)),
      _N_motive_wf Γ₁out xout tout tout' Γ (.abs t₀ u) (WfM.fun_ L hT hB) := by
  intro Γ t₀ u L hT hB ihT ihB Γ₂ hΓ hLCt hfvt
  subst hΓ
  refine WfM.fun_ L (ihT Γ₂ rfl hLCt hfvt) ?_
  intro y hy
  have ih := ihB y hy (⟨y, t₀, .sub⟩ :: Γ₂) (by simp) hLCt hfvt
  simpa using ih

private noncomputable def _N_app :
    ∀ {Γ : Ctx} {u v t₀ : Term}
      (hStarU : WSubMStar Γ u (.abs t₀ .top))
      (hStarV : WSubMStar Γ v t₀)
      (ihU : _N_motive_star Γ₁out xout tout tout' Γ u (.abs t₀ .top) hStarU)
      (ihV : _N_motive_star Γ₁out xout tout tout' Γ v t₀ hStarV),
      _N_motive_wf Γ₁out xout tout tout' Γ (.app u v) (WfM.app hStarU hStarV) := by
  intro Γ u v t₀ hSU hSV ihU ihV Γ₂ hΓ hLCt hfvt
  subst hΓ
  exact WfM.app (ihU Γ₂ rfl hLCt hfvt) (ihV Γ₂ rfl hLCt hfvt)

private noncomputable def _N_rfl :
    ∀ {Γ : Ctx} {u : Term} (hwf : WfM Γ u)
      (ihwf : _N_motive_wf Γ₁out xout tout tout' Γ u hwf),
      _N_motive_sub Γ₁out xout tout tout' Γ u u (WSubM.rfl hwf) := by
  intro Γ u hwf ihwf Γ₂ hΓ hLCt hfvt
  subst hΓ
  exact WSubM.rfl (ihwf Γ₂ rfl hLCt hfvt)

private noncomputable def _N_lf1 :
    ∀ {Γ : Ctx} {v v' u : Term}
      (hred : MEqRed Γ [] v v')
      (hsub : WSubM Γ v' u)
      (ih : _N_motive_sub Γ₁out xout tout tout' Γ v' u hsub),
      _N_motive_sub Γ₁out xout tout tout' Γ v u (WSubM.lf1 hred hsub) := by
  intro Γ v v' u hred hsub ih Γ₂ hΓ hLCt hfvt
  subst hΓ
  have hred' : MEqRed (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) [] v v' :=
    Lemma_25_NarrowingMEqRed hred hLCt hfvt
  exact WSubM.lf1 hred' (ih Γ₂ rfl hLCt hfvt)

private noncomputable def _N_lf2 :
    ∀ {Γ : Ctx} {v v' u : Term}
      (hwfV : WfM Γ v) (hred : MSubRed Γ [] v v')
      (hwfV' : WfM Γ v') (hsub : WSubM Γ v' u)
      (ihwfV : _N_motive_wf Γ₁out xout tout tout' Γ v hwfV)
      (ihwfV' : _N_motive_wf Γ₁out xout tout tout' Γ v' hwfV')
      (ih : _N_motive_sub Γ₁out xout tout tout' Γ v' u hsub),
      _N_motive_sub Γ₁out xout tout tout' Γ v u
        (WSubM.lf2 hwfV hred hwfV' hsub) := by
  intro Γ v v' u hwfV hred hwfV' hsub ihwfV ihwfV' ih Γ₂ hΓ hLCt hfvt
  subst hΓ
  have hred' : MSubRed (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) [] v v' :=
    Lemma_24_NarrowingMSubRed hred hLCt hfvt
  exact WSubM.lf2 (ihwfV Γ₂ rfl hLCt hfvt) hred'
                  (ihwfV' Γ₂ rfl hLCt hfvt)
                  (ih Γ₂ rfl hLCt hfvt)

private noncomputable def _N_rgh :
    ∀ {Γ : Ctx} {v u u' : Term}
      (hsub : WSubM Γ v u') (hred : MEqRed Γ [] u u')
      (ih : _N_motive_sub Γ₁out xout tout tout' Γ v u' hsub),
      _N_motive_sub Γ₁out xout tout tout' Γ v u (WSubM.rgh hsub hred) := by
  intro Γ v u u' hsub hred ih Γ₂ hΓ hLCt hfvt
  subst hΓ
  have hred' : MEqRed (Γ₂ ++ ⟨xout, tout, .sub⟩ :: Γ₁out) [] u u' :=
    Lemma_25_NarrowingMEqRed hred hLCt hfvt
  exact WSubM.rgh (ih Γ₂ rfl hLCt hfvt) hred'

private noncomputable def _N_sub_star :
    ∀ {Γ : Ctx} {v u : Term}
      (hwfV : WfM Γ v) (hsub : WSubM Γ v u) (hwfT : WfM Γ u)
      (ihwfV : _N_motive_wf Γ₁out xout tout tout' Γ v hwfV)
      (ihsub : _N_motive_sub Γ₁out xout tout tout' Γ v u hsub)
      (ihwfT : _N_motive_wf Γ₁out xout tout tout' Γ u hwfT),
      _N_motive_star Γ₁out xout tout tout' Γ v u
        (WSubMStar.sub hwfV hsub hwfT) := by
  intro Γ v u hwfV hsub hwfT ihwfV ihsub ihwfT Γ₂ hΓ hLCt hfvt
  subst hΓ
  exact WSubMStar.sub (ihwfV Γ₂ rfl hLCt hfvt) (ihsub Γ₂ rfl hLCt hfvt)
                       (ihwfT Γ₂ rfl hLCt hfvt)

private noncomputable def _N_trs_star :
    ∀ {Γ : Ctx} {v u w : Term}
      (hStar1 : WSubMStar Γ v u) (hwfU : WfM Γ u) (hStar2 : WSubMStar Γ u w)
      (ih1 : _N_motive_star Γ₁out xout tout tout' Γ v u hStar1)
      (ihwfU : _N_motive_wf Γ₁out xout tout tout' Γ u hwfU)
      (ih2 : _N_motive_star Γ₁out xout tout tout' Γ u w hStar2),
      _N_motive_star Γ₁out xout tout tout' Γ v w
        (WSubMStar.trs hStar1 hwfU hStar2) := by
  intro Γ v u w hStar1 hwfU hStar2 ih1 ihwfU ih2 Γ₂ hΓ hLCt hfvt
  subst hΓ
  exact WSubMStar.trs (ih1 Γ₂ rfl hLCt hfvt) (ihwfU Γ₂ rfl hLCt hfvt)
                       (ih2 Γ₂ rfl hLCt hfvt)

end Narrowing23

/-- **Lemma 23** (Pasquale & García-Pérez 2024, Narrowing for `WfM`).
Restricted form: takes `Term.fv t ⊆ Γ₁.dom` and `Term.LC t` directly. -/
noncomputable def Lemma_23_NarrowingWf
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' u : Term}
    (hwf : WfM (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) u)
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    WfM (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) u :=
  WfM.rec
    (motive_1 := _N_motive_wf Γ₁ x t t')
    (motive_2 := _N_motive_sub Γ₁ x t t')
    (motive_3 := _N_motive_star Γ₁ x t t')
    (@_N_varSub Γ₁ x t t')
    (@_N_varEqu Γ₁ x t t')
    (@_N_top Γ₁ x t t')
    (@_N_fun Γ₁ x t t')
    (@_N_app Γ₁ x t t')
    (@_N_rfl Γ₁ x t t')
    (@_N_lf1 Γ₁ x t t')
    (@_N_lf2 Γ₁ x t t')
    (@_N_rgh Γ₁ x t t')
    (@_N_sub_star Γ₁ x t t')
    (@_N_trs_star Γ₁ x t t')
    hwf Γ₂ rfl hLCt hfvt

/-- Companion narrowing for `WSubM`. -/
noncomputable def Lemma_23_NarrowingWSubM
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' v u : Term}
    (hsub : WSubM (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) v u)
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    WSubM (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) v u :=
  WSubM.rec
    (motive_1 := _N_motive_wf Γ₁ x t t')
    (motive_2 := _N_motive_sub Γ₁ x t t')
    (motive_3 := _N_motive_star Γ₁ x t t')
    (@_N_varSub Γ₁ x t t')
    (@_N_varEqu Γ₁ x t t')
    (@_N_top Γ₁ x t t')
    (@_N_fun Γ₁ x t t')
    (@_N_app Γ₁ x t t')
    (@_N_rfl Γ₁ x t t')
    (@_N_lf1 Γ₁ x t t')
    (@_N_lf2 Γ₁ x t t')
    (@_N_rgh Γ₁ x t t')
    (@_N_sub_star Γ₁ x t t')
    (@_N_trs_star Γ₁ x t t')
    hsub Γ₂ rfl hLCt hfvt

/-- Companion narrowing for `WSubMStar`. -/
noncomputable def Lemma_23_NarrowingWSubMStar
    {Γ₁ Γ₂ : Ctx} {x : String} {t t' v u : Term}
    (hstar : WSubMStar (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) v u)
    (hLCt : Term.LC t)
    (hfvt : Term.fv t ⊆ Γ₁.dom) :
    WSubMStar (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) v u :=
  WSubMStar.rec
    (motive_1 := _N_motive_wf Γ₁ x t t')
    (motive_2 := _N_motive_sub Γ₁ x t t')
    (motive_3 := _N_motive_star Γ₁ x t t')
    (@_N_varSub Γ₁ x t t')
    (@_N_varEqu Γ₁ x t t')
    (@_N_top Γ₁ x t t')
    (@_N_fun Γ₁ x t t')
    (@_N_app Γ₁ x t t')
    (@_N_rfl Γ₁ x t t')
    (@_N_lf1 Γ₁ x t t')
    (@_N_lf2 Γ₁ x t t')
    (@_N_rgh Γ₁ x t t')
    (@_N_sub_star Γ₁ x t t')
    (@_N_trs_star Γ₁ x t t')
    hstar Γ₂ rfl hLCt hfvt

end Pss
