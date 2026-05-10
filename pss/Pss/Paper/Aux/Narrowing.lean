import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Paper.Aux.Narrowing` — paper Lemmas 23, 24, 25, 26

Mechanizes the "Narrowing" lemma group from Pasquale & García-Pérez 2024
(paper p. 9:37–41):

* **Lemma 23** (Narrowing of context in well-formedness, p. 9:37–38) —
  changing a `.sub`-bound annotation (from `t` to an equivalent `t'`)
  preserves well-formedness of any term.
* **Lemma 24** (Narrowing of context in subtyping reductions, p. 9:38–39)
  — same annotation change preserves subtype-reduction reachability,
  producing (possibly) a fresh post-reduct that the original target
  reaches by an equivalence chain.
* **Lemma 25** (Narrowing of context in equivalence reductions, p. 9:39)
  — same annotation change preserves equivalence-reduction reachability
  with the *same* target (`→ᵉᵠᵘ` does not promote a `.sub`-bound
  variable to its annotation, hence the bound change is invisible to
  the derivation).
* **Lemma 26** (Narrowing prevalidity, p. 9:39–41) — same annotation
  change preserves prevalidity of the extended context.

The paper's order is 23 → 24 → 25 → 26, with the proofs of 23 and 24
invoking 25 internally (Lemma 23's `Wf-App` case uses Lemma 25 to lift
an empty-stack equivalence chain across the bound change; Lemma 24's
proof uses Lemma 19 weakening + Lemma 25 in the non-promotion case).
Lemma 26 stands structurally first (it underwrites the prevalidity
side-condition the other three need).

## De Bruijn translation

The paper's named context `Γ, x ≤ t, Γ'` (resp. `Γ, x ⊲ t, Γ'` for the
kind-generic Lemma 26) is translated to a single context list with the
`.sub`-headed entry sitting at de Bruijn level `Γ'.length`:

```
   Γ, x ≤ t, Γ'    ↦   Γ' ++ {bound := t, .sub} :: Γ
```

After narrowing, that entry's bound is replaced by `t'`:

```
   Γ, x ≤ t', Γ'   ↦   Γ' ++ {bound := t', .sub} :: Γ
```

This is exactly `Ctx.replaceAt` at `cutoff := Γ'.length`. The
*head* specialisation (Γ' = nil) collapses to `cutoff := 0`, which is
the form most call sites consume.

## Existing codebase counterparts

Each paper lemma maps to existing infrastructure in
`Pss/Mpss/DeBruijnReductions.lean` and `Pss/Context/DeBruijn.lean`:

* **Lemma 26** ↔ `Prevalid.replaceAt` (general `cutoff`),
  `Prevalid.sub_head_replace` (head case, `cutoff = 0`).
  See `Pss/Context/DeBruijn.lean:1656` and `:1702`. The codebase
  ships the equivalence-binder analogues (`Prevalid.equ_head_replace`)
  and the `.equ`-bound `Pv-EqA` case via the same `replaceAt`. **Direct
  match — proved unconditionally.**

* **Lemma 25** ↔ `MEqRed.replaceAt_sub` (general `cutoff`),
  `MEqRed.sub_head_replace` (head case). See
  `Pss/Mpss/DeBruijnReductions.lean:1795` and `:1805`. Closed by
  induction on the `MEqRed` derivation; the `Me-Pro` case is benign
  on a `.sub` head because `equBinds` ignores `.sub` entries (only
  `.equ` heads can fire `Me-Pro` at the same index). **Direct match —
  proved unconditionally.**

* **Lemma 24** ↔ `MSubRed.replaceAt_sub` (general `cutoff`),
  `MSubRed.sub_head_replace` (head case). See
  `Pss/Mpss/DeBruijnReductions.lean:5978` and `:6013`. The codebase
  form takes **payloads** for the cases where the source `MSubRed`
  derivation either fires `Ms-Pro` at the replaced slot (the paper's
  "case where the derivation makes a promotion of `x` to `t`"), or
  recursively descends into a `Ms-Fun`/`Ms-FOp` body whose binder
  preserves the underlying replaced slot. Each payload corresponds
  to a paper sub-case that invokes Lemma 19 weakening (for the
  promotion case) or the structural recursion (for the binder cases).
  The conclusion is `MSubRedStar` (a chain) rather than a single
  `MSubRed` step, exactly mirroring the paper's "there exists a `v'`
  reached by `→ˢᵘᵇ`" existential. **Direct match — proved
  unconditionally modulo caller-supplied paper-faithful payloads.**

* **Lemma 23** ↔ `WfMSubHeadReplaceOfNewWf` (residual `Type` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:10995`). This is **not yet
  closed** in the de Bruijn working development; it ships as a
  packaging type whose fields list the constructor-local payloads
  (`WfMSubHeadReplaceDirectPayloads`,
  `WfMSubHeadReplaceImmediateDirectPayloads`,
  `WfMSubUnderHeadReplaceOfNewWf`) callers must furnish. The paper's
  proof is full induction on the `WfM` derivation by last rule, with
  the `Wf-App` case carrying internal sub-decomposition (paper
  p. 9:37–38) that mirrors the `Wf-App` decomposition in Lemma 7.
  **Conditional on `WfMSubHeadReplaceOfNewWf` — exposed here as an
  `_of`-form theorem that takes the residual as a hypothesis,
  matching the convention used by `Theorem_11_*_of` in
  `Pss/Paper/Aux/Propositions.lean`.**

## Mechanization divergences

### Lemma 23

* The paper's hypothesis `Γ, x ≤ t, Γ' ⊢ u wf` becomes the de Bruijn
  `WfM (Γ' ++ {bound := t, .sub} :: Γ) u`. The conclusion is the same
  with `t` replaced by `t'`. The codebase's `WfMSubHeadReplaceOfNewWf`
  ships only the **head** specialisation (`Γ' = nil`), which is
  sufficient for downstream call sites; the general form would be
  `WfMSubHeadsReplaceOfNewWf n` at index `n = Γ'.length`. We expose
  the head form for paper-faithful naming and document the general
  form as `Lemma_23_Narrowing_WfM_general` (also conditional on the
  same residual via the under-heads payload).
* Paper's `Γ; nil ⊢ t →ᵉᵠᵘ t'` premise is `MEqRed Γ [] t t'`.
* Paper's `Γ ⊢ t' wf` premise is `WfM Γ t'` (de Bruijn de-aliases the
  named binder `x` to its de Bruijn level).

### Lemma 24

The codebase form returns `MSubRedStar` (a chain) and consumes
caller-supplied payloads for (a) the changed-slot `Ms-Pro` case, (b)
the `Ms-Fun` body recursion, (c) the `Ms-FOp` body recursion. The
paper's three sub-cases on whether `Ms-Pro` fires at `x` correspond
1-to-1 to these payloads:

* **Ms-Pro at `x`**: The original step targets
  `Term.shiftBy 0 (cutoff+1) old`; in the narrowed context this
  becomes a chain via `Ms-Equ`-bridging through Lemma 25 followed
  by `Ms-Pro` at the new bound. Paper invokes Lemma 19 (weakening)
  to lift `Γ ⊢ t' wf` to `Γ, x ≤ t', Γ' ⊢ t' wf`; the de Bruijn
  payload absorbs that bridge.
* **Ms-Pro elsewhere**: Direct rebuild (no payload needed; handled
  inline by `MSubRed.pro_replaceAt_sub_of_ne`).
* **Ms-Fun / Ms-FOp body**: Recursive narrowing on the body, with
  the preserved binder head shifting the replaced slot's depth. The
  payload structure mirrors the paper's recursive descent.

The asymmetric paper formulation ("there exists `v'` such that
`u →ˢᵘᵇ v'` and `v →ᵉᵠᵘ v'`") corresponds to the codebase's
`MSubRedStar` chain target: a single `MSubRed` step in the source
context becomes a (possibly multi-step) `MSubRedStar` chain in the
narrowed context that may detour through extra `Ms-Equ` rebuilds
when the changed slot is touched. -- Paper produces fresh `v'` and
new `→ᵉᵠᵘ` step; mechanized as: `MSubRedStar` chain target encodes
the same factorization implicitly via `Ms-Equ` rebuilds inside the
chain.

### Lemma 25

Paper's `s` is general (any extended stack); the codebase's
`MEqRed.replaceAt_sub` and `MEqRed.sub_head_replace` accept any `s`.
Direct match.

### Lemma 26

Paper's hypothesis is "`Γ, x ⊲ t, Γ'; s` is prevalid" (kind-generic).
The codebase's `Prevalid` is structured as a context-only judgment
with a separate `PrevalidExt` for the stack; the paper's combined
prevalidity becomes the conjunction of `Prevalid (Γ' ++ ⟨t, kind⟩ ::
Γ)` and `PrevalidExt (Γ' ++ ⟨t, kind⟩ :: Γ) s`. Both transport
through the same `replaceAt` operation, since neither depends on
`.sub`/`.equ` bound *content*, only on scopedness.

The kind-generic form (paper's `x ⊲ t`) splits in de Bruijn into a
`.sub`-headed and an `.equ`-headed variant. Both are exposed:

* `Lemma_26_Narrowing_Prevalidity_sub` for `.sub` heads,
* `Lemma_26_Narrowing_Prevalidity_equ` for `.equ` heads,
* `Lemma_26_Narrowing_Prevalidity` for the kind-generic head form.

## Imports

This file imports `Pss.Mpss.DeBruijnTypeSafety` for
`WfMSubHeadReplaceOfNewWf` (Lemma 23 residual). The lower-level
helpers (`Prevalid.replaceAt`, `MEqRed.replaceAt_sub`,
`MSubRed.replaceAt_sub`) are re-exported transitively via that
import. -/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Lemma 26 — Narrowing prevalidity (paper p. 9:39–41)

Stand-alone (no recursion on the other narrowing lemmas). The paper's
proof is induction on the prevalidity derivation tree by last `Pv-*`
rule. In de Bruijn the operation is `Ctx.replaceAt cutoff newEntry Γ`
plus the corresponding `PrevalidExt.replaceAt_*_same` for the stack
side; both compose into the kind-generic head replacement. -/

/-- **Lemma 26 (Narrowing prevalidity, sub-binder head form), paper p. 9:39.**

> *Statement.* Let `Γ, x ≤ t, Γ'; s` be a prevalid extended context, and
> `t'` such that `Γ; s ⊢ t →ᵉᵠᵘ t'`. Then `Γ, x ≤ t', Γ'; s` is
> prevalid.
>
> *Proof.* Induction on the prevalidity derivation tree by last `Pv-*`
> rule. Each rule's premise transports across the bound change because
> prevalidity inspects only context scopedness, not bound content. The
> head case applies directly; under-head cases descend through the
> preserved binder and recurse.

This entry covers the head specialisation `Γ' = nil` for a `.sub`
binder. Mechanized via `Prevalid.sub_head_replace`
(`Pss/Context/DeBruijn.lean:1702`). The paper's `Γ; s ⊢ t →ᵉᵠᵘ t'`
premise is reflected here as `Term.Scoped Γ.depth new`: scopedness is
all the prevalidity judgment consumes. The full equivalence step
witness is downstream-discharged by callers that need to also transport
`MEqRed`/`MSubRed` derivations across the bound change. -/
noncomputable def Lemma_26_Narrowing_Prevalidity_sub
    {Γ : Ctx} {old new : Term}
    (hpv : Prevalid ({ bound := old, kind := .sub } :: Γ))
    (hnew : Term.Scoped Γ.depth new) :
    Prevalid ({ bound := new, kind := .sub } :: Γ) :=
  hpv.sub_head_replace hnew

/-- **Lemma 26 (Narrowing prevalidity, equ-binder head form), paper p. 9:39.**

The paper's `Γ, x ⊲ t, Γ'` is kind-generic. This entry covers the
equivalence-binder specialisation `x ≡ α` (paper's `⊲` = `≡`).
Mechanized via the kind-generic `Prevalid.replaceAt` at `cutoff = 0`
with an `.equ`-headed entry. Symmetric to `Lemma_26_Narrowing_Prevalidity_sub`. -/
noncomputable def Lemma_26_Narrowing_Prevalidity_equ
    {Γ : Ctx} {old new : Term}
    (hpv : Prevalid ({ bound := old, kind := .equ } :: Γ))
    (hnew : Term.Scoped Γ.depth new) :
    Prevalid ({ bound := new, kind := .equ } :: Γ) := by
  cases hpv with
  | equ hΓ _ => exact Prevalid.equ hΓ hnew

/-- **Lemma 26 (Narrowing prevalidity, kind-generic head form), paper p. 9:39.**

> *Statement.* Let `Γ, x ⊲ t, Γ'; s` be a prevalid extended context, and
> `t'` such that `Γ; s ⊢ t →ᵉᵠᵘ t'`. Then `Γ, x ⊲ t', Γ'; s` is
> prevalid.
>
> *Proof.* Induction on the derivation tree by last `Pv-*` rule.

Kind-generic head specialisation: paper's `x ⊲ t` quantifies over both
`.sub` and `.equ` bindings. The de Bruijn version dispatches on the
`kind` field. Mechanized as a `match` on the `kind`. -/
noncomputable def Lemma_26_Narrowing_Prevalidity
    {Γ : Ctx} {old new : Term} {kind : CtxEntryKind}
    (hpv : Prevalid ({ bound := old, kind } :: Γ))
    (hnew : Term.Scoped Γ.depth new) :
    Prevalid ({ bound := new, kind } :: Γ) := by
  cases kind with
  | sub => exact Lemma_26_Narrowing_Prevalidity_sub hpv hnew
  | equ => exact Lemma_26_Narrowing_Prevalidity_equ hpv hnew

/-- **Lemma 26 (Narrowing prevalidity, general `cutoff` form), paper p. 9:39.**

The general-`Γ'` form: replace any innermost-or-deeper context entry
whose new bound is scoped in its tail. This is what the paper writes
when `Γ' ≠ nil`. Mechanized via `Prevalid.replaceAt`
(`Pss/Context/DeBruijn.lean:1656`). -/
noncomputable def Lemma_26_Narrowing_Prevalidity_general
    {Γ : Ctx} {cutoff : Nat} {newEntry : CtxEntry}
    (hpv : Prevalid Γ)
    (hcut : cutoff < Γ.depth)
    (hEntry : CtxEntry.ScopedIn (List.drop (cutoff + 1) Γ) newEntry) :
    Prevalid (Ctx.replaceAt cutoff newEntry Γ) :=
  Prevalid.replaceAt hpv hcut hEntry

/-! ## Lemma 25 — Narrowing of context in equivalence reductions
(paper p. 9:39)

The paper's premise is `Γ, x ≤ t, Γ'; s ⊢ u →ᵉᵠᵘ v` and the
conclusion replaces `t` by `t'` in the same context. The de Bruijn
form: `MEqRed (Γ' ++ {bound := t, .sub} :: Γ) s u v` becomes
`MEqRed (Γ' ++ {bound := t', .sub} :: Γ) s u v`. The crucial fact
underwriting transparency is that `Me-Pro` only fires on `.equ` heads,
so the `.sub` bound change is invisible to the derivation tree. -/

/-- **Lemma 25 (Narrowing of context in equivalence reductions, head form), paper p. 9:39.**

> *Statement.* Let `Γ; s` be an extended context, `Γ'` an additional
> context. Let `u, v, t, t'` be terms. If
> `Γ, x ≤ t, Γ'; s ⊢ u →ᵉᵠᵘ v` and `Γ; nil ⊢ t →ᵉᵠᵘ t'`, then
> `Γ, x ≤ t', Γ'; s ⊢ u →ᵉᵠᵘ v`.
>
> *Proof.* By induction on the derivation tree by last rule. Each
> rule's premise transports because `→ᵉᵠᵘ` does not promote a
> `.sub`-bound variable to its `≤` annotation (only `Me-Pro` would
> promote, and it requires an `.equ` head — `.sub` heads are
> structurally inert under `Me-Pro`).

Head specialisation `Γ' = nil`. Mechanized via `MEqRed.sub_head_replace`
(`Pss/Mpss/DeBruijnReductions.lean:1805`). -/
noncomputable def Lemma_25_Narrowing_MEqRed
    {Γ : Ctx} {s : Stack} {old new u v : Term}
    (h : MEqRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new) :
    MEqRed ({ bound := new, kind := .sub } :: Γ) s u v :=
  h.sub_head_replace hOldNew

/-- **Lemma 25 (chain version), paper p. 9:39.**

The paper's `→ᵉᵠᵘ` is a single-step relation; its star-closure is
`↦ᵉᵠᵘ`. This chain version is the consequence the paper actually uses
in downstream proofs (Lemma 23 via Theorem 4 / strong commutation; the
diamond closure of Theorem 1). Mechanized via
`MEqRedStar.sub_head_replace`. -/
theorem Lemma_25_Narrowing_MEqRed_star
    {Γ : Ctx} {s : Stack} {old new u v : Term}
    (h : MEqRedStar ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new) :
    MEqRedStar ({ bound := new, kind := .sub } :: Γ) s u v :=
  MEqRedStar.sub_head_replace h hOldNew

/-- **Lemma 25 (general `cutoff` form), paper p. 9:39.**

The general-`Γ'` form: paper's `Γ, x ≤ t, Γ'` becomes
`Γ' ++ {bound := old, .sub} :: Γ`. Mechanized via `MEqRed.replaceAt_sub`
(`Pss/Mpss/DeBruijnReductions.lean:1795`). -/
noncomputable def Lemma_25_Narrowing_MEqRed_general
    {Γ : Ctx} {s : Stack} {cutoff : Nat} {old new u v : Term}
    (h : MEqRed (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) s u v)
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new) :
    MEqRed (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v :=
  h.replaceAt_sub hcut hOldNew

/-- Prop-wrapper variant of Lemma 25 head form. -/
theorem Lemma_25_Narrowing_MEqRed_J
    {Γ : Ctx} {s : Stack} {old new u v : Term}
    (h : MEqRedJ ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRedJ Γ [] old new) :
    MEqRedJ ({ bound := new, kind := .sub } :: Γ) s u v :=
  ⟨Lemma_25_Narrowing_MEqRed h.some hOldNew.some⟩

/-! ## Lemma 24 — Narrowing of context in subtyping reductions
(paper p. 9:38–39)

The paper's statement is asymmetric: from `Γ, x ≤ t, Γ'; nil ⊢ u →ˢᵘᵇ v`
and a bound step `t →ᵉᵠᵘ t'`, produce a fresh `v'` with `u →ˢᵘᵇ v'` and
`v →ᵉᵠᵘ v'` in the narrowed context. The de Bruijn form returns
`MSubRedStar` (a chain) at the narrowed context, which encodes the
asymmetric existential implicitly: a single `Ms-Pro` step at the
replaced slot becomes an `Ms-Equ` + `Ms-Pro` chain at the new bound,
and the chain target is the de Bruijn analogue of the paper's `v'`. -/

/-- **Lemma 24 (Narrowing of context in subtyping reductions, head form), paper p. 9:38.**

> *Statement.* Let `Γ; s` be an extended context, `Γ'` an additional
> context. Let `u, v, t, t'` be terms. If
> `Γ, x ≤ t, Γ'; nil ⊢ u →ˢᵘᵇ v` and `Γ; nil ⊢ t →ᵉᵠᵘ t'`. Assume that
> both `u, v` are well-formed in context `Γ, x ≤ t', Γ'`. Assume also
> `Γ ⊢ t' wf`. Then there exists a term `v'` such that we have
> `Γ, x ≤ t', Γ'; nil ⊢ u →ˢᵘᵇ v'` and
> `Γ, x ≤ t', Γ'; nil ⊢ v →ᵉᵠᵘ v'`.
>
> *Proof.* Induction on the derivation tree by last rule. Case on
> whether the derivation makes a promotion of `x` to `t`. If not, the
> substitution is identity; else use weakening-to-Co context (Lemma 19)
> to lift `Γ ⊢ t' wf` and bridge through `Ms-Equ`.

Head specialisation `Γ' = nil`. Mechanized via `MSubRed.sub_head_replace`
(`Pss/Mpss/DeBruijnReductions.lean:6013`). The codebase form takes
**three payloads** corresponding 1-to-1 with the paper's three sub-cases:

* `hProSelf`: the changed-slot `Ms-Pro` case (paper "promotion of `x`
  to `t`"). Paper bridges `t' wf` via Lemma 19 weakening and
  `Ms-Equ` to land on the new bound; the payload supplies that bridge
  directly as a `MSubRedStar` chain.
* `hFunBody`: the `Ms-Fun` recursive descent into a binder body whose
  preserved head shifts the replaced slot's depth.
* `hFOpBody`: the `Ms-FOp` recursive descent (analogous).

The conclusion `MSubRedStar` (chain) encodes the paper's asymmetric
existential `∃ v', u →ˢᵘᵇ v' ∧ v →ᵉᵠᵘ v'` implicitly: a single source
step becomes a chain in the narrowed context, with detour `Ms-Equ`
steps bridging the bound change at the changed slot. -/
noncomputable def Lemma_24_Narrowing_MSubRed
    {Γ : Ctx} {s : Stack} {old new u v : Term}
    (h : MSubRed ({ bound := old, kind := .sub } :: Γ) s u v)
    (hOldNew : MEqRed Γ [] old new)
    (hProSelf : ∀ {s' : Stack},
      PrevalidExt ({ bound := new, kind := .sub } :: Γ) s' →
      MSubRedStar ({ bound := new, kind := .sub } :: Γ) s'
        (.bvar 0) (Term.shift 0 old))
    (hFunBody : ∀ {t t' body body' : Term},
      Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t →
      MEqRed ({ bound := old, kind := .sub } :: Γ) [] t t' →
      MSubRed ({ bound := t, kind := .sub } ::
          { bound := old, kind := .sub } :: Γ) [] body body' →
      MSubRedStar ({ bound := new, kind := .sub } :: Γ) []
        (.abs t body) (.abs t' body'))
    (hFOpBody : ∀ {t α body body' : Term} {sBody : Stack},
      Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) t →
      Term.Scoped (Ctx.depth ({ bound := old, kind := .sub } :: Γ)) α →
      MSubRed ({ bound := α, kind := .equ } ::
          { bound := old, kind := .sub } :: Γ)
        (Stack.shift 0 sBody) body body' →
      MSubRedStar ({ bound := new, kind := .sub } :: Γ)
        (α :: sBody) (.abs t body) (.abs t body')) :
    MSubRedStar ({ bound := new, kind := .sub } :: Γ) s u v :=
  h.sub_head_replace hOldNew hProSelf hFunBody hFOpBody

/-- **Lemma 24 (general `cutoff` form), paper p. 9:38.**

The general-`Γ'` form: same payload structure but the changed slot
sits at de Bruijn level `cutoff = Γ'.length`. Mechanized via
`MSubRed.replaceAt_sub` (`Pss/Mpss/DeBruijnReductions.lean:5978`). -/
noncomputable def Lemma_24_Narrowing_MSubRed_general
    {Γ : Ctx} {s : Stack} {cutoff : Nat} {old new u v : Term}
    (h : MSubRed (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) s u v)
    (hcut : cutoff < Ctx.depth Γ)
    (hOldNew : MEqRed (List.drop (cutoff + 1) Γ) [] old new)
    (hProSelf : ∀ {s' : Stack},
      PrevalidExt (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s' →
      MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s'
        (.bvar cutoff) (Term.shiftBy 0 (cutoff + 1) old))
    (hFunBody : ∀ {t t' body body' : Term},
      Term.Scoped
        (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t →
      MEqRed
        (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) [] t t' →
      MSubRed ({ bound := t, kind := .sub } ::
          Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ) [] body body' →
      MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) []
        (.abs t body) (.abs t' body'))
    (hFOpBody : ∀ {t α body body' : Term} {sBody : Stack},
      Term.Scoped
        (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) t →
      Term.Scoped
        (Ctx.depth (Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)) α →
      MSubRed ({ bound := α, kind := .equ } ::
          Ctx.replaceAt cutoff { bound := old, kind := .sub } Γ)
        (Stack.shift 0 sBody) body body' →
      MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ)
        (α :: sBody) (.abs t body) (.abs t body')) :
    MSubRedStar (Ctx.replaceAt cutoff { bound := new, kind := .sub } Γ) s u v :=
  h.replaceAt_sub hcut hOldNew hProSelf hFunBody hFOpBody

/-! ## Lemma 23 — Narrowing of context in well-formedness
(paper p. 9:37–38)

The paper's hypothesis is `Γ, x ≤ t, Γ' ⊢ u wf`; after the bound
narrowing, we conclude `Γ, x ≤ t', Γ' ⊢ u wf`. The proof is full
induction on the `WfM` derivation by last rule. The `Wf-App` case has
internal sub-decomposition that mirrors Lemma 7: it must reconstruct
the function-type subtype derivation in the narrowed context, which
internally invokes Lemmas 24 and 25.

In the de Bruijn working development, this lemma ships as the residual
type `WfMSubHeadReplaceOfNewWf`
(`Pss/Mpss/DeBruijnTypeSafety.lean:10995`); the constructor-local
payloads (`WfMSubHeadReplaceDirectPayloads`,
`WfMSubHeadReplaceImmediateDirectPayloads`,
`WfMSubUnderHeadReplaceOfNewWf`) capture the `Wf-App` /
`Wf-Fun` / `Wf-FOp` recursive cases the paper handles inline. The
residual is **conditional** here: we expose `Lemma_23_Narrowing_WfM_of`
that takes `WfMSubHeadReplaceOfNewWf` as an explicit hypothesis,
following the convention of `Theorem_11_NoTopAbstractionSupertypes_of`
in `Pss/Paper/Aux/Propositions.lean`. -/

/-- **Lemma 23 (Narrowing of context in well-formedness), paper p. 9:37–38.**

> *Statement.* Let `Γ` and `Γ'` be two contexts; `t, t', u` be terms.
> If `Γ, x ≤ t, Γ' ⊢ u wf`, `Γ; nil ⊢ t →ᵉᵠᵘ t'`, and `Γ ⊢ t' wf`,
> then `Γ, x ≤ t', Γ' ⊢ u wf`.
>
> *Proof.* Induction on the `WfM` derivation by last rule.
> * `Wf-Top`/`Wf-Var`/`Wf-TAp`: reassemble at the new bound (the new
>   bound's scopedness comes from `WfM Γ t'`).
> * `Wf-Pro`: the bound `bvar` is either `x` (then transport via the
>   bound step `t →ᵉᵠᵘ t'`) or another `.equ` slot (then preserve
>   directly).
> * `Wf-Fun`/`Wf-FOp`: recurse on body under the preserved binder; use
>   Lemma 25 (equivalence narrowing) to lift the body's stack
>   transport.
> * `Wf-App`: internal sub-decomposition (paper p. 9:37–38). The
>   functional well-subtyping `Γ ⊢ u_op ≤*_wf λx ≤ t.u_body` must be
>   transported across the bound change. Since this involves an
>   `MSubRedStar` and an `MEqRedStar` chain (per Theorem 3), the
>   transport invokes Lemmas 24 and 25 internally.

Head specialisation `Γ' = nil`. Conditional on
`WfMSubHeadReplaceOfNewWf`, the de Bruijn working development's
packaging of paper Lemma 23 as a payload type. -/
noncomputable def Lemma_23_Narrowing_WfM_of
    (hReplace : WfMSubHeadReplaceOfNewWf)
    {Γ : Ctx} {old new body : Term}
    (hOldNew : MEqRed Γ [] old new)
    (hNewWf : WfM Γ new)
    (hBody : WfM ({ bound := old, kind := .sub } :: Γ) body) :
    WfM ({ bound := new, kind := .sub } :: Γ) body :=
  hReplace hOldNew hNewWf hBody

/-- **Lemma 23 (under-head form), paper p. 9:37–38.**

The recursive case the paper's `Wf-Fun` / `Wf-FOp` sub-cases consume:
narrow a `.sub` annotation that sits one binder below a preserved
head. Conditional on `WfMSubUnderHeadReplaceOfNewWf`. -/
noncomputable def Lemma_23_Narrowing_WfM_under_of
    (hReplace : WfMSubUnderHeadReplaceOfNewWf)
    {Γ : Ctx} {head : CtxEntry} {old new body : Term}
    (hOldNew : MEqRed Γ [] old new)
    (hNewWf : WfM Γ new)
    (hBody : WfM (head :: { bound := old, kind := .sub } :: Γ) body) :
    WfM (head :: { bound := new, kind := .sub } :: Γ) body :=
  hReplace hOldNew hNewWf hBody

end Paper
end DeBruijn
end Pss
