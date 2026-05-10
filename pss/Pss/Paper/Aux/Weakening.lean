import Pss.Mpss.DeBruijnWellFormed

/-! # `Pss.Paper.Aux.Weakening` — paper Lemmas 19, 20, 21, 22

Mechanizes the "Weakening of context" lemma group from Pasquale &
García-Pérez 2024 (paper p. 9:34 – p. 9:37):

* **Lemma 19** (Weakening of context, p. 9:34) — the bundled statement
  spanning all nine paper judgments.
* **Lemma 20** (auxiliary, p. 9:34) — the three `wf`-only conjuncts.
* **Lemma 21** (subtyping reduction, p. 9:36) — the `→ˢᵘᵇ` conjunct.
* **Lemma 22** (equivalence reduction, p. 9:37) — the `→ᵉᵠᵘ` conjunct.

The paper's proof of Lemma 19 (p. 9:34) reads:

> *Proof.* Note: this lemma is a group of different lemmas which are
> proved separately. This proof dispatches the proof of each of these
> lemmas to their respective proof.

Accordingly, Lemma 19 is built here by aggregating Lemmas 20–22 plus
the chain-shaped variants for `→*ˢᵘᵇ` and `→*ᵉᵠᵘ` and the diagrammatic
`≤` / `≤*` variants.

## De Bruijn translation

The paper writes the weakening's "outer" extension as a logical-context
suffix `Γ, Γ'` and the new stack as the operand append `s @ s'`. In de
Bruijn there are no names; the extension `Γ'` becomes a list of
`CtxEntry` values prepended to `Γ` (innermost head first), and weakening
shifts every free index by `Γ'.length`.

The paper's stack append `s @ s'` specialises in the codebase to the
**stack-trivial** form: the original stack `s` is shifted across the
new bindings, and no extra operands are pushed (`s' = nil`). The
non-trivial `s'` case requires translating `Me-Fun` derivations to
`Me-FOp` per the paper's Me-Fun / Me-FOp arithmetic on p. 9:37; the de
Bruijn working development factors that translation through dedicated
stack-lift helpers (`meq_equ_head_stack_lift_*` in
`Pss/Mpss/DeBruijnTransitivityElim.lean`) rather than through Lemma 19.
-- Paper handwaves; mechanized as: stack-trivial `s' = nil`
specialization, matching the existing `MEqRedJ.weaken_head` family.

## Existing codebase counterparts (reused, not re-proved)

The thin wrappers below dispatch to the existing weakening machinery:

* `WfM.weaken_head`, `WSubM.weaken_head`, `WSubMStar.weaken_head`,
  `WEquM.weaken_head`, `WEquMStar.weaken_head`
  (`Pss/Mpss/DeBruijnWellFormed.lean`).
* `MEqRedJ.weaken_head`, `MSubRedJ.weaken_head`,
  `MEqRedStar.weaken_head`, `MSubRedStar.weaken_head`
  (`Pss/Mpss/DeBruijnReductions.lean`).

The paper-faithful entry points iterate the head-extension `Γ'.length`
times to build the full weakening from `Γ` to `Γ' ++ Γ`. Each iteration
shifts the term/stack by one; after `Γ'.length` iterations the total
shift is `Term.shiftBy 0 Γ'.length` (and likewise for the stack).
-/

namespace Pss
namespace DeBruijn
namespace Paper

namespace Weakening

/-! ## Stack-shift composition

Helper lemma that the de Bruijn working development does not export
explicitly. Used to align iterated stack shifts with `Stack.shiftBy 0 n`.
-/

/-- One-step `Stack.shift 0` after an `n`-step `Stack.shiftBy 0` is the
same as a single `(n+1)`-step shift. The pointwise version of
`Term.shiftBy_compose` lifted through `List.map`. -/
private theorem stack_shift_compose (n : Nat) (s : Stack) :
    Stack.shift 0 (Stack.shiftBy 0 n s) = Stack.shiftBy 0 (n + 1) s := by
  induction s with
  | nil => rfl
  | cons α rest ih =>
      change
        Term.shift 0 (Term.shiftBy 0 n α) ::
            Stack.shift 0 (Stack.shiftBy 0 n rest) =
          Term.shiftBy 0 (n + 1) α :: Stack.shiftBy 0 (n + 1) rest
      have hAlpha : Term.shift 0 (Term.shiftBy 0 n α) =
          Term.shiftBy 0 (n + 1) α := by
        simpa [Term.shift] using Term.shiftBy_compose 0 n 1 α
      simp [hAlpha, ih]

/-- `Stack.shiftBy 0 0` is the identity. -/
private theorem stack_shiftBy_zero_id (s : Stack) :
    Stack.shiftBy 0 0 s = s := by
  induction s with
  | nil => rfl
  | cons α rest ih =>
      change Term.shiftBy 0 0 α :: Stack.shiftBy 0 0 rest = α :: rest
      simp [Term.shiftBy_zero_id, ih]

/-! ## Per-judgment iterated head-extension

Each helper takes the original judgment in `Γ`, an extension `Γ'`, and
the prevalidity of the extended context (which carries through to the
iterated extension). Every helper is a structural induction on `Γ'`
whose step uses the corresponding `weaken_head` from the existing
development.
-/

/-- Iterated head-extension of an extended-context prevalidity witness.
Builds `PrevalidExt (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)` from
`PrevalidExt Γ s` and `Prevalid (Γ' ++ Γ)`. -/
noncomputable def PrevalidExt_appendCtx {Γ : Ctx} (Γ' : Ctx) {s : Stack}
    (hpvE : PrevalidExt Γ s) (hpv : Prevalid (Γ' ++ Γ)) :
    PrevalidExt (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, stack_shiftBy_zero_id] using hpvE
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep : PrevalidExt (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s) :=
        ih hpvTail
      have hHead : PrevalidExt (head :: (Γ'' ++ Γ))
          (Stack.shift 0 (Stack.shiftBy 0 Γ''.length s)) :=
        hStep.weaken_head hpv
      have hStack : Stack.shift 0 (Stack.shiftBy 0 Γ''.length s) =
          Stack.shiftBy 0 (Γ''.length + 1) s :=
        stack_shift_compose Γ''.length s
      simpa [List.length_cons, hStack, List.cons_append] using hHead

/-- **Lemma 20.1, paper p. 9:34** (well-formedness conjunct). Iterated
head-extension lifts `Γ ⊢ u wf` to `Γ' ++ Γ ⊢ u wf`, shifting the term
through the new bindings.

This is the de Bruijn analogue of the paper's `Γ ⊢ u wf → Γ, Γ' ⊢ u wf`. -/
noncomputable def WfM_appendCtx {Γ : Ctx} (Γ' : Ctx) {t : Term}
    (h : WfM Γ t) (hpv : Prevalid (Γ' ++ Γ)) :
    WfM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length t) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep : WfM (Γ'' ++ Γ) (Term.shiftBy 0 Γ''.length t) :=
        ih hpvTail
      have hHead : WfM (head :: (Γ'' ++ Γ))
          (Term.shift 0 (Term.shiftBy 0 Γ''.length t)) :=
        hStep.weaken_head hpv hpvTail
      have hCompose :
          Term.shift 0 (Term.shiftBy 0 Γ''.length t) =
            Term.shiftBy 0 (Γ''.length + 1) t := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 t
      simpa [List.length_cons, hCompose, List.cons_append] using hHead

/-- **Lemma 20.2, paper p. 9:34** (well-subtyping conjunct). Iterated
head-extension lifts `Γ ⊢ u ≤_wf v` to `Γ' ++ Γ ⊢ u ≤_wf v`. -/
noncomputable def WSubM_appendCtx {Γ : Ctx} (Γ' : Ctx) {u v : Term}
    (h : WSubM Γ u v) (hpv : Prevalid (Γ' ++ Γ)) :
    WSubM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u)
      (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hHead := hStep.weaken_head hpv hpvTail
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hComposeU, hComposeV, List.cons_append] using hHead

/-- **Lemma 20.3, paper p. 9:34** (transitive well-subtyping conjunct).
Iterated head-extension lifts `Γ ⊢ u ≤*_wf v` to `Γ' ++ Γ ⊢ u ≤*_wf v`. -/
noncomputable def WSubMStar_appendCtx {Γ : Ctx} (Γ' : Ctx) {u v : Term}
    (h : WSubMStar Γ u v) (hpv : Prevalid (Γ' ++ Γ)) :
    WSubMStar (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u)
      (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hHead := hStep.weaken_head hpv hpvTail
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hComposeU, hComposeV, List.cons_append] using hHead

/-- Well-equivalence at the well-formed level (the `≤_wf` analogue for
equivalence) iterated through head-extension. Although the paper's
Lemma 19 statement does not list `WEquM` explicitly, the codebase ships
its weakening alongside the others; we expose it here for parity with
`WSubM_appendCtx` so callers needing equivalence-at-wf-level have a
paper-shaped entry point. -/
noncomputable def WEquM_appendCtx {Γ : Ctx} (Γ' : Ctx) {u v : Term}
    (h : WEquM Γ u v) (hpv : Prevalid (Γ' ++ Γ)) :
    WEquM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u)
      (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hHead := hStep.weaken_head hpv hpvTail
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hComposeU, hComposeV, List.cons_append] using hHead

/-- Transitive well-equivalence weakening. Same shape as
`WSubMStar_appendCtx`. -/
noncomputable def WEquMStar_appendCtx {Γ : Ctx} (Γ' : Ctx) {u v : Term}
    (h : WEquMStar Γ u v) (hpv : Prevalid (Γ' ++ Γ)) :
    WEquMStar (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u)
      (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hHead := hStep.weaken_head hpv hpvTail
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hComposeU, hComposeV, List.cons_append] using hHead

/-- **Lemma 21, paper p. 9:36** (subtyping-reduction conjunct).
Iterated head-extension lifts `Γ; s ⊢ u →ˢᵘᵇ v` to `Γ' ++ Γ; s_lifted ⊢ ...`,
shifting the stack and term through the new bindings.

Paper restates the conclusion at stack `s` (no extra `s'` operands —
Lemma 21 is the stack-faithful conjunct, i.e. the `s' = nil`
specialisation). -/
theorem MSubRedJ_appendCtx {Γ : Ctx} (Γ' : Ctx) {s : Stack} {u v : Term}
    (h : MSubRedJ Γ s u v) (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) :
    MSubRedJ (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, stack_shiftBy_zero_id, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep : MSubRedJ (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s)
          (Term.shiftBy 0 Γ''.length u) (Term.shiftBy 0 Γ''.length v) :=
        ih hpvTail
      have hpvEIter : PrevalidExt (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s) :=
        PrevalidExt_appendCtx Γ'' hpvE hpvTail
      have hHead := hStep.weaken_head hpvEIter hpv
      have hStack : Stack.shift 0 (Stack.shiftBy 0 Γ''.length s) =
          Stack.shiftBy 0 (Γ''.length + 1) s :=
        stack_shift_compose Γ''.length s
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hStack, hComposeU, hComposeV, List.cons_append]
        using hHead

/-- Star-closure variant of Lemma 21: `↦ˢᵘᵇ` weakening through
context-extension. -/
theorem MSubRedStar_appendCtx {Γ : Ctx} (Γ' : Ctx) {s : Stack} {u v : Term}
    (h : MSubRedStar Γ s u v) (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) :
    MSubRedStar (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, stack_shiftBy_zero_id, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hpvEIter : PrevalidExt (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s) :=
        PrevalidExt_appendCtx Γ'' hpvE hpvTail
      have hHead := hStep.weaken_head hpvEIter hpv
      have hStack : Stack.shift 0 (Stack.shiftBy 0 Γ''.length s) =
          Stack.shiftBy 0 (Γ''.length + 1) s :=
        stack_shift_compose Γ''.length s
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hStack, hComposeU, hComposeV, List.cons_append]
        using hHead

/-- **Lemma 22, paper p. 9:37** (equivalence-reduction conjunct).
Iterated head-extension lifts `Γ; s ⊢ u →ᵉᵠᵘ v` to `Γ' ++ Γ; s_lifted ⊢ ...`,
shifting the stack and term through the new bindings.

The paper states this conjunct with the new stack `s @ s'`; the de
Bruijn working development restricts to the stack-trivial case
(`s' = nil`), as documented in the file docstring. -/
theorem MEqRedJ_appendCtx {Γ : Ctx} (Γ' : Ctx) {s : Stack} {u v : Term}
    (h : MEqRedJ Γ s u v) (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) :
    MEqRedJ (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, stack_shiftBy_zero_id, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hpvEIter : PrevalidExt (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s) :=
        PrevalidExt_appendCtx Γ'' hpvE hpvTail
      have hHead := hStep.weaken_head hpvEIter hpv
      have hStack : Stack.shift 0 (Stack.shiftBy 0 Γ''.length s) =
          Stack.shiftBy 0 (Γ''.length + 1) s :=
        stack_shift_compose Γ''.length s
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hStack, hComposeU, hComposeV, List.cons_append]
        using hHead

/-- Star-closure variant of Lemma 22: `↦ᵉᵠᵘ` weakening. -/
theorem MEqRedStar_appendCtx {Γ : Ctx} (Γ' : Ctx) {s : Stack} {u v : Term}
    (h : MEqRedStar Γ s u v) (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) :
    MEqRedStar (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) := by
  induction Γ' with
  | nil =>
      simpa [List.length_nil, stack_shiftBy_zero_id, Term.shiftBy_zero_id] using h
  | cons head Γ'' ih =>
      have hpvTail : Prevalid (Γ'' ++ Γ) := Prevalid.tail hpv
      have hStep := ih hpvTail
      have hpvEIter : PrevalidExt (Γ'' ++ Γ) (Stack.shiftBy 0 Γ''.length s) :=
        PrevalidExt_appendCtx Γ'' hpvE hpvTail
      have hHead := hStep.weaken_head hpvEIter hpv
      have hStack : Stack.shift 0 (Stack.shiftBy 0 Γ''.length s) =
          Stack.shiftBy 0 (Γ''.length + 1) s :=
        stack_shift_compose Γ''.length s
      have hComposeU :
          Term.shift 0 (Term.shiftBy 0 Γ''.length u) =
            Term.shiftBy 0 (Γ''.length + 1) u := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 u
      have hComposeV :
          Term.shift 0 (Term.shiftBy 0 Γ''.length v) =
            Term.shiftBy 0 (Γ''.length + 1) v := by
        simpa [Term.shift] using Term.shiftBy_compose 0 Γ''.length 1 v
      simpa [List.length_cons, hStack, hComposeU, hComposeV, List.cons_append]
        using hHead

end Weakening

/-! ## Paper-faithful named entry points

These wrappers expose the per-judgment helpers under names that match
the paper's lemma numbering. -/

/-- **Lemma 20 (Weakening of context — auxiliary), paper p. 9:34.**

> *Statement.* Let `Γ` and `Γ'` be two logical contexts such that
> `Γ, Γ'` is prevalid. Let `u` and `v` be terms. We have the following
> relations:
> 1. If `Γ ⊢ u wf` then `Γ, Γ' ⊢ u wf`.
> 2. If `Γ ⊢ u ≤_wf v` then `Γ, Γ' ⊢ u ≤_wf v`.
> 3. If `Γ ⊢ u ≤*_wf v` then `Γ, Γ' ⊢ u ≤*_wf v`.
>
> *Proof.* By combined induction on the derivation tree. -- The paper
> explains that the three relations cross-reference (via `Wf-App`),
> forcing combined induction; in the de Bruijn development this is
> already discharged once at the `_combined` motive layer in
> `Pss/Mpss/DeBruijnWellFormed.lean` and reused here.

Bundled as a structure with one field per conjunct. The premise `hpv`
witnesses prevalidity of the combined context `Γ' ++ Γ`. -/
structure Lemma_20_Weakening_Aux (Γ' Γ : Ctx) (hpv : Prevalid (Γ' ++ Γ))
    (u v : Term) where
  /-- Conjunct 1: well-formedness. -/
  wf : WfM Γ u →
    WfM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u)
  /-- Conjunct 2: well-subtyping. -/
  subWf : WSubM Γ u v →
    WSubM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)
  /-- Conjunct 3: transitive well-subtyping. -/
  subStarWf : WSubMStar Γ u v →
    WSubMStar (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)

/-- The proved Lemma 20: dispatches each conjunct to the per-judgment
helper. -/
noncomputable def Lemma_20_Weakening_Aux.proved (Γ' Γ : Ctx)
    (hpv : Prevalid (Γ' ++ Γ)) (u v : Term) :
    Lemma_20_Weakening_Aux Γ' Γ hpv u v where
  wf h := Weakening.WfM_appendCtx Γ' h hpv
  subWf h := Weakening.WSubM_appendCtx Γ' h hpv
  subStarWf h := Weakening.WSubMStar_appendCtx Γ' h hpv

/-- **Lemma 21 (Weakening of context — subtyping reduction),
paper p. 9:36.**

> *Statement.* Let `Γ; s` and `Γ'` be two contexts such that
> `Γ, Γ'; s` is prevalid. Let `u` and `v` be terms. If `Γ; s ⊢ u →ˢᵘᵇ v`
> then `Γ, Γ'; s ⊢ u →ˢᵘᵇ v`.
>
> *Proof.* By induction on the derivation tree of `Γ; s ⊢ u →ˢᵘᵇ v`. -- In
> de Bruijn the discharge is via iterated head-extension, which collapses
> to repeated `MSubRedJ.weaken_head`.

The de Bruijn translation shifts `s` through the new bindings:
`Stack.shiftBy 0 Γ'.length s`. -/
theorem Lemma_21_Weakening_SubtypingReduction
    {Γ' Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s)
    (h : MSubRedJ Γ s u v) :
    MSubRedJ (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) :=
  Weakening.MSubRedJ_appendCtx Γ' h hpv hpvE

/-- **Lemma 22 (Weakening of context — equivalence reduction),
paper p. 9:37.**

> *Statement.* Let `Γ; s` and `Γ'; s'` be two extended contexts such
> that `Γ, Γ'; s @ s'` is prevalid. Let `u` and `v` be terms. If
> `Γ; s ⊢ u →ᵉᵠᵘ v` then `Γ, Γ'; s @ s' ⊢ u →ᵉᵠᵘ v`.
>
> *Proof.* By induction on the derivation tree of `Γ; s ⊢ u →ᵉᵠᵘ v`. -- In
> de Bruijn the discharge is via iterated head-extension, which collapses
> to repeated `MEqRedJ.weaken_head`.

The de Bruijn translation specialises `s'` to nil (the stack-trivial
form) — see file docstring. The result stack is
`Stack.shiftBy 0 Γ'.length s`. -- Paper handwaves; mechanized as:
`s' = nil` per the file-level "De Bruijn translation" note. -/
theorem Lemma_22_Weakening_EquivalenceReduction
    {Γ' Γ : Ctx} {s : Stack} {u v : Term}
    (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s)
    (h : MEqRedJ Γ s u v) :
    MEqRedJ (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v) :=
  Weakening.MEqRedJ_appendCtx Γ' h hpv hpvE

/-- **Lemma 19 (Weakening of context), paper p. 9:34.**

> *Statement.* Let `Γ; s` and `Γ'; s'` be two extended contexts such
> that `Γ, Γ'; s @ s'` is prevalid. Let `u` and `v` be terms. We have
> the following relations:
> 1. If `Γ ⊢ u wf` then `Γ, Γ' ⊢ u wf`.
> 2. If `Γ ⊢ u ≤_wf v` then `Γ, Γ' ⊢ u ≤_wf v`.
> 3. If `Γ ⊢ u ≤*_wf v` then `Γ, Γ' ⊢ u ≤*_wf v`.
> 4. If `Γ; s ⊢ u →ˢᵘᵇ v` then `Γ, Γ'; s ⊢ u →ˢᵘᵇ v`.
> 5. If `Γ; s ⊢ u ↦ˢᵘᵇ v` then `Γ, Γ'; s ⊢ u ↦ˢᵘᵇ v`.
> 6. If `Γ; s ⊢ u →ᵉᵠᵘ v` then `Γ, Γ'; s @ s' ⊢ u →ᵉᵠᵘ v`.
> 7. If `Γ; s ⊢ u ↦ᵉᵠᵘ v` then `Γ, Γ'; s @ s' ⊢ u ↦ᵉᵠᵘ v`.
>
> *Proof.* Note: this lemma is a group of different lemmas which are
> proved separately. This proof dispatches the proof of each of these
> lemmas to their respective proof.
> * `wf`/`≤_wf`/`≤*_wf` cases: discharged via Lemma 20.
> * `→ˢᵘᵇ`/`↦ˢᵘᵇ` cases: discharged via Lemma 21 (and its star closure).
> * `→ᵉᵠᵘ`/`↦ᵉᵠᵘ` cases: discharged via Lemma 22 (and its star closure).

Bundled as a structure with one field per paper conjunct. The premise
`hpv` witnesses prevalidity of the combined context `Γ' ++ Γ`; the
extended-context premise `hpvE` provides the original `PrevalidExt Γ s`
which is needed for the stack-bearing conjuncts. -/
structure Lemma_19_Weakening (Γ' Γ : Ctx) (s : Stack) (u v : Term)
    (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) where
  /-- Conjunct 1 (paper): `Γ ⊢ u wf → Γ, Γ' ⊢ u wf`. Mechanized via
  Lemma 20.1 (`Weakening.WfM_appendCtx`). -/
  wf : WfM Γ u →
    WfM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u)
  /-- Conjunct 2 (paper): `Γ ⊢ u ≤_wf v → Γ, Γ' ⊢ u ≤_wf v`. Mechanized
  via Lemma 20.2 (`Weakening.WSubM_appendCtx`). -/
  subWf : WSubM Γ u v →
    WSubM (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)
  /-- Conjunct 3 (paper): `Γ ⊢ u ≤*_wf v → Γ, Γ' ⊢ u ≤*_wf v`. Mechanized
  via Lemma 20.3 (`Weakening.WSubMStar_appendCtx`). -/
  subStarWf : WSubMStar Γ u v →
    WSubMStar (Γ' ++ Γ) (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)
  /-- Conjunct 4 (paper): `Γ; s ⊢ u →ˢᵘᵇ v → Γ, Γ'; s ⊢ u →ˢᵘᵇ v`.
  Mechanized via Lemma 21 (`Weakening.MSubRedJ_appendCtx`). -/
  subRed : MSubRedJ Γ s u v →
    MSubRedJ (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)
  /-- Conjunct 5 (paper): `Γ; s ⊢ u ↦ˢᵘᵇ v → Γ, Γ'; s ⊢ u ↦ˢᵘᵇ v`.
  Mechanized via the star closure of Lemma 21
  (`Weakening.MSubRedStar_appendCtx`). -/
  subRedStar : MSubRedStar Γ s u v →
    MSubRedStar (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)
  /-- Conjunct 6 (paper): `Γ; s ⊢ u →ᵉᵠᵘ v → Γ, Γ'; s @ s' ⊢ u →ᵉᵠᵘ v`.
  Mechanized via Lemma 22 (`Weakening.MEqRedJ_appendCtx`) at `s' = nil`
  per the file docstring. -/
  equRed : MEqRedJ Γ s u v →
    MEqRedJ (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)
  /-- Conjunct 7 (paper): `Γ; s ⊢ u ↦ᵉᵠᵘ v → Γ, Γ'; s @ s' ⊢ u ↦ᵉᵠᵘ v`.
  Mechanized via the star closure of Lemma 22
  (`Weakening.MEqRedStar_appendCtx`) at `s' = nil`. -/
  equRedStar : MEqRedStar Γ s u v →
    MEqRedStar (Γ' ++ Γ) (Stack.shiftBy 0 Γ'.length s)
      (Term.shiftBy 0 Γ'.length u) (Term.shiftBy 0 Γ'.length v)

/-- The proved Lemma 19: dispatches each conjunct to its named auxiliary
lemma per the paper's "this proof dispatches the proof of each of these
lemmas to their respective proof". -/
noncomputable def Lemma_19_Weakening.proved (Γ' Γ : Ctx) (s : Stack)
    (u v : Term) (hpv : Prevalid (Γ' ++ Γ))
    (hpvE : PrevalidExt Γ s) :
    Lemma_19_Weakening Γ' Γ s u v hpv hpvE :=
  let aux := Lemma_20_Weakening_Aux.proved Γ' Γ hpv u v
  { wf := aux.wf
    subWf := aux.subWf
    subStarWf := aux.subStarWf
    subRed := fun h =>
      Lemma_21_Weakening_SubtypingReduction hpv hpvE h
    subRedStar := fun h =>
      Weakening.MSubRedStar_appendCtx Γ' h hpv hpvE
    equRed := fun h =>
      Lemma_22_Weakening_EquivalenceReduction hpv hpvE h
    equRedStar := fun h =>
      Weakening.MEqRedStar_appendCtx Γ' h hpv hpvE }

end Paper
end DeBruijn
end Pss
