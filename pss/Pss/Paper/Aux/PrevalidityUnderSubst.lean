import Pss.Mpss.DeBruijnTypeSafety

/-! # `Pss.Paper.Aux.PrevalidityUnderSubst` — paper Lemma 28

Mechanizes "Substitution preserves prevalidity" from Pasquale &
García-Pérez 2024 (paper p. 9:40).

**Lemma 28 (Substitution preserves prevalidity, paper p. 9:40).** Let
`Γ, x ⊲ t, Γ'; s` be an extended context.
1. If `Γ, x ⊲ t, Γ'; s` is prevalid then `Γ, Γ'[x\t]; s[x\t]` is prevalid.
2. If `Γ, x ⊲ t, Γ'`    is prevalid then `Γ, Γ'[x\t]`        is prevalid.

The paper proof (p. 9:40–41) is induction on the prevalidity derivation
by last `Pv-*` rule (`Pv-Emp`, `Pv-Ctx`, `Pv-EqA`, `Pv-Nil`, `Pv-Sta`).
The second conjunct ("we prove the first result, the second is similar")
is dispatched analogously.

## De Bruijn translation

The paper writes `Γ, x ⊲ t, Γ'` (named-binder form). In de Bruijn there
are no names; the `x` position becomes a de Bruijn level corresponding
to `Γ'.length`. The paper's substitution `Γ'[x\t]` translates to the
codebase's `Ctx.instantiateBetaPrefix t Γ'.length Γ'` operation: each
preserved head's bound is `Term.instantiate`d at the appropriate de
Bruijn level (the head closest to the removed `.sub` entry receives
cutoff `0`; each newer preserved head receives one additional shift).
The paper's stack substitution `s[x\t]` becomes
`Stack.instantiate Γ'.length (Term.shiftBy 0 Γ'.length t) s`.

So the paper-faithful statement of Lemma 28 in de Bruijn form is:
* (1) `PrevalidExt (Γ' ++ {bound := t, .sub} :: Γ) s →`
      `PrevalidExt (Ctx.instantiateBetaPrefix t Γ'.length Γ' ++ Γ)`
                  `(Stack.instantiate Γ'.length (Term.shiftBy 0 Γ'.length t) s)`.
* (2) `Prevalid (Γ' ++ {bound := t, .sub} :: Γ) →`
      `Prevalid (Ctx.instantiateBetaPrefix t Γ'.length Γ' ++ Γ)`.

## Mechanization divergence — explicit `WSubMStar Γ t t` premise

The paper's `Prevalid` (defined in Figure 1, p. 9:4) requires `Γ ⊢ t wf`
on every `Pv-Ctx` or `Pv-EqA` introduction (i.e. paper-prevalidity bundles
well-formedness of every annotation into the context-prevalidity
judgment itself). Hence the paper can extract `Γ ⊢ t wf` "for free" from
prevalidity of `Γ, x ⊲ t, Γ'` via outer-context inspection.

The codebase's `Prevalid` (`Pss/Context/DeBruijn.lean:1624`) is **weaker**:
it carries only `Term.Scoped Γ.depth t` for every `.sub` or `.equ`
bound entry, with `WfM` tracked as a separate judgment. This is a deliberate
mechanization choice — the de Bruijn working development decouples
scope-tracking from well-formedness so that scope-only manipulations
(shifts, instantiations) do not depend on the WfM induction.

To recover the paper's "prevalidity gives WfM of `t`" implication, we
expose Lemma 28's de Bruijn form with an explicit `WSubMStar Γ t t`
premise. This witness is exactly what the paper's prevalidity provides
(reflexive well-subtyping of the dropped bound). At every concrete call
site downstream of Lemma 28, the caller first establishes
`WfM Γ t` (and `WSubMStar Γ t t` by reflexivity) from whatever stronger
context judgment is in scope, then invokes Lemma 28.

-- Paper has prevalidity-implies-`t`-wf as a structural property of
   `Prevalid`; mechanized as: explicit `WSubMStar Γ t t` premise (which
   the codebase's separate WfM tracking forces).

## Existing codebase counterparts (reused, not re-proved)

* **Logical-context conjunct (paper Lemma 28.2)**:
  `BetaInstantiationPreservesPrevalidPrefix` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:603`.
* **Extended-context conjunct (paper Lemma 28.1)**:
  `BetaInstantiationPreservesPrevalidExtUnderHeads` at
  `Pss/Mpss/DeBruijnTypeSafety.lean:646`.

Both are `noncomputable def` because `Prevalid` and `PrevalidExt` are
`Type`-valued. The aliases below are also `noncomputable def` to
preserve the constructive content. -/

namespace Pss
namespace DeBruijn
namespace Paper

/-! ## Lemma 28 — Substitution preserves prevalidity (paper p. 9:40) -/

/-- **Lemma 28.1 (Substitution preserves prevalidity, extended-context
form), paper p. 9:40.**

> *Statement.* Let `Γ, x ⊲ t, Γ'; s` be an extended context. If
> `Γ, x ⊲ t, Γ'; s` is prevalid then `Γ, Γ'[x\t]; s[x\t]` is prevalid.
>
> *Proof.* By induction on the derivation tree of `Γ, x ⊲ t, Γ'; s`
> prevalid. We distinguish cases on the last rule used.
> * `Pv-Nil` (`s = ε`): `Γ, x ⊲ t, Γ'` prevalid; close by IH (Lemma 28.2)
>   plus `Pv-Nil`.
> * `Pv-Sta` (`s = α :: s₀`): `Γ, x ⊲ t, Γ'; s₀` prevalid and `α` is
>   well-formed in `Γ, x ⊲ t, Γ'`. By IH on `s₀`, `Γ, Γ'[x\t]; s₀[x\t]`
>   prevalid. By a separate substitution lemma on `wf`, `α[x\t]` is
>   well-formed in `Γ, Γ'[x\t]`. Reassemble with `Pv-Sta`.

The de Bruijn translation discharges via
`BetaInstantiationPreservesPrevalidExtUnderHeads`: the paper's `Γ'`
becomes the prefix `heads` (innermost head first), the dropped `.sub`
entry sits between `heads` and `Γ`, and the substitution argument is
`t` itself (paper writes `Γ'[x\t]`).

The paper's "prevalidity implies `Γ ⊢ t wf`" implication is recovered
from the explicit `hSubt : WSubMStar Γ t t` premise (see file docstring
"Mechanization divergence"). -/
noncomputable def Lemma_28_SubstitutionPreservesPrevalidity_extended
    {Γ : Ctx} (Γ' : Ctx) {s : Stack} {t : Term}
    (hSubt : WSubMStar Γ t t)
    (hpv : PrevalidExt (Γ' ++ { bound := t, kind := .sub } :: Γ) s) :
    PrevalidExt (Ctx.instantiateBetaPrefix t Γ'.length Γ' ++ Γ)
      (Stack.instantiate Γ'.length (Term.shiftBy 0 Γ'.length t) s) :=
  BetaInstantiationPreservesPrevalidExtUnderHeads (heads := Γ')
    (n := Γ'.length) rfl hSubt hpv

/-- **Lemma 28.2 (Substitution preserves prevalidity, logical-context
form), paper p. 9:40.**

> *Statement.* If `Γ, x ⊲ t, Γ'` is prevalid then `Γ, Γ'[x\t]` is
> prevalid.
>
> *Proof.* "We prove the first result, the second is similar." Induction
> on the derivation tree of `Γ, x ⊲ t, Γ'` prevalid. We distinguish cases
> on the last rule used.
> * `Pv-Emp` (`Γ' = ε`, contradicting `x ⊲ t ∈ Γ, x ⊲ t, Γ'`): impossible
>   in this conjunct's setup; the actual `Pv-Emp` analogue handles the
>   degenerate `Γ' = ε` case where the substitution becomes the identity
>   on the outer `Γ` after stripping `x ⊲ t`.
> * `Pv-Ctx` (`Γ' = Γ₀, y ≤ tᵧ`): by IH on `Γ₀`, `Γ, Γ₀[x\t]` prevalid;
>   close with `Pv-Ctx` after substituting `tᵧ[x\t]`.
> * `Pv-EqA` (`Γ' = Γ₀, y ≡ α`): by IH on `Γ₀`, `Γ, Γ₀[x\t]` prevalid;
>   close with `Pv-EqA` after substituting `α[x\t]`.

The de Bruijn translation discharges via
`BetaInstantiationPreservesPrevalidPrefix`: same shape as Lemma 28.1
modulo the extended-stack conjunct. The paper's "prevalidity implies
`Γ ⊢ t wf`" implication is recovered from the explicit
`hSubt : WSubMStar Γ t t` premise (see file docstring "Mechanization
divergence"). -/
noncomputable def Lemma_28_SubstitutionPreservesPrevalidity_logical
    {Γ : Ctx} (Γ' : Ctx) {t : Term}
    (hSubt : WSubMStar Γ t t)
    (hpv : Prevalid (Γ' ++ { bound := t, kind := .sub } :: Γ)) :
    Prevalid (Ctx.instantiateBetaPrefix t Γ'.length Γ' ++ Γ) :=
  BetaInstantiationPreservesPrevalidPrefix (heads := Γ') hSubt hpv

end Paper
end DeBruijn
end Pss
