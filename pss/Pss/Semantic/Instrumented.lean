import Pss.Syntax

/-!
# The instrumented declarative system

§1 of `pss/docs/03-revised-proof.md`: Figure 1's declarative system under the
paper's §3.4 reading — *"Any derivation of `t ≤wf u` only compares well-formed
subterms"* — made explicit: every `SubI` node carries well-formedness premises
for the terms it mentions, so the fundamental theorem (doc Theorem 6.2) can
consume them rule-locally via doc Lemma 3.3. The uninstrumented Figure 1
(`Pss.Declarative`) is left untouched; this is a fresh mutual family.

Two instrumentation choices are deliberately *unpacked* rather than carried as
opaque wf premises (cf. the doc's §6 DS-APP case and §9 watchpoints):

* `SubI.app` carries the two W-APP instrumentations of its endpoints as four
  `WellSubI` premises, with the bounds `s`, `s'` as constructor arguments.
  The fundamental theorem's DS-APP case needs the *semantic content of the
  sub-derivations* (`Γ ⊨ t ≤ λx≤s.Top`, `Γ ⊨ u ≤ s`, and the primed pair) —
  an opaque `WfI Γ (.app t u)` premise would only yield `Γ ⊨ t(u) wf` as its
  IH, which is not enough to run the doc's (a)/(a′)/(c)/(d) chain.
* `SubI.eapp` relates a well-formed redex to a well-formed contractum: if the
  contractum's wf is not derivable, that rule instance simply isn't available
  (doc §1).

The W-rules themselves are Figure 1's verbatim; their instrumentation is
inherited through `WellSubI`, which is what W-APP consumes (doc §1: "This is
the relation the W-rules actually consume, so it is the right relation for
type safety").
-/

namespace Pss

mutual

/-- `Γ wf` — instrumented context well-formedness (W-GAM1, W-GAM2). -/
inductive CtxWfI : Ctx → Prop where
  /-- `∅ wf` (W-GAM1). -/
  | nil : CtxWfI []
  /-- `Γ wf, Γ ⊢ t wf ⟹ Γ, x ≤ t wf` (W-GAM2). -/
  | cons {Γ : Ctx} {t : Term} : CtxWfI Γ → WfI Γ t → CtxWfI (t :: Γ)

/-- `Γ ⊢ t wf` — instrumented well-formedness (Figure 1's W-rules verbatim;
the instrumentation lives in `SubI`). -/
inductive WfI : Ctx → Term → Prop where
  /-- `Γ wf, x ∈ dom(Γ) ⟹ Γ ⊢ x wf` (W-VAR). -/
  | var {Γ : Ctx} {x : Nat} : CtxWfI Γ → x < Γ.length → WfI Γ (.var x)
  /-- `Γ wf ⟹ Γ ⊢ Top wf` (W-TOP). -/
  | top {Γ : Ctx} : CtxWfI Γ → WfI Γ .top
  /-- `Γ, x ≤ t ⊢ u wf ⟹ Γ ⊢ λx ≤ t. u wf` (W-FUN). -/
  | fn {Γ : Ctx} {t u : Term} : WfI (t :: Γ) u → WfI Γ (.lam t u)
  /-- `Γ ⊢ t ≤wf λx ≤ s. Top, Γ ⊢ u ≤wf s ⟹ Γ ⊢ t(u) wf` (W-APP). -/
  | app {Γ : Ctx} {t u s : Term} :
      WellSubI Γ t .le (.lam s .top) → WellSubI Γ u .le s →
      WfI Γ (.app t u)

/-- `Γ ⊢ t ⊲wf u` — instrumented well-subtyping (W-SUB). -/
inductive WellSubI : Ctx → Term → Rel → Term → Prop where
  /-- `Γ ⊢ t wf, u wf, Γ ⊢ t ⊲ u ⟹ Γ ⊢ t ⊲wf u` (W-SUB). -/
  | sub {Γ : Ctx} {t u : Term} {r : Rel} :
      WfI Γ t → WfI Γ u → SubI Γ t r u → WellSubI Γ t r u

/-- `Γ ⊢ t ⊲ u` — instrumented declarative subtyping (doc §1): Figure 1's
DS-rules, each carrying `WfI` premises for the terms it mentions. -/
inductive SubI : Ctx → Term → Rel → Term → Prop where
  /-- DS-TRANS. Figure 1 already carries the middle term's wf; the endpoints'
  semantic content rides in the premises' IHs (doc Theorem 5.1 needs nothing
  else — composition is set-theoretic at a fixed index). -/
  | trans {Γ : Ctx} {s t u : Term} {r : Rel} :
      SubI Γ s r t → SubI Γ t r u → WfI Γ t → SubI Γ s r u
  /-- DS-SYM. The premise's semantic ≡ already carries `=β` and both wf. -/
  | symm {Γ : Ctx} {t u : Term} : SubI Γ u .eq t → SubI Γ t .eq u
  /-- DS-EQ. -/
  | eq {Γ : Ctx} {t u : Term} : SubI Γ t .eq u → SubI Γ t .le u
  /-- DS-VAR, carrying W-VAR's premises for the mentioned variable. -/
  | var {Γ : Ctx} {x : Nat} :
      CtxWfI Γ → x < Γ.length → SubI Γ (.var x) .eq (.var x)
  /-- DS-TOP. -/
  | top {Γ : Ctx} : CtxWfI Γ → SubI Γ .top .eq .top
  /-- DS-FUN, carrying wf of both λs (doc §6, DS-FUN case: both endpoints'
  wf feed Lemma 3.3 and the ≡-form). Bound is *invariant* (§3.3). -/
  | fn {Γ : Ctx} {t t' u u' : Term} {r : Rel} :
      SubI Γ t .eq t' → SubI (t :: Γ) u r u' →
      WfI Γ (.lam t u) → WfI Γ (.lam t' u') →
      SubI Γ (.lam t u) r (.lam t' u')
  /-- DS-APP, carrying both endpoints' W-APP instrumentations *unpacked*
  (see module docstring). The doc's DS-APP case names the bounds `s`, `s'`:
  the bound-conversion chain (c) `S =β A =β A′ =β S′` connects them. -/
  | app {Γ : Ctx} {t t' u u' s s' : Term} {r : Rel} :
      SubI Γ t r t' → SubI Γ u .eq u' →
      WellSubI Γ t .le (.lam s .top) → WellSubI Γ u .le s →
      WellSubI Γ t' .le (.lam s' .top) → WellSubI Γ u' .le s' →
      SubI Γ (.app t u) r (.app t' u')
  /-- DS-EAPP, relating a well-formed redex to a well-formed contractum
  (doc §1: if the contractum's wf is not derivable, this rule instance is
  simply unavailable). -/
  | eapp {Γ : Ctx} {t u s : Term} :
      WfI Γ (.app (.lam t u) s) → WfI Γ (u.subst1 s) →
      SubI Γ (.app (.lam t u) s) .eq (u.subst1 s)
  /-- DS-ETOP, carrying wf of the left endpoint (consumed by doc Lemma 3.3
  for the membership half). -/
  | etop {Γ : Ctx} {t : Term} : WfI Γ t → SubI Γ t .le .top
  /-- DS-EVAR, carrying the context discipline of the mentioned variable.
  Semantically both halves are read directly off the goodness of `γx`
  (doc §6, DS-EVAR case). -/
  | evar {Γ : Ctx} {x : Nat} {t : Term} :
      Ctx.Bound Γ x t → CtxWfI Γ → SubI Γ (.var x) .le t

end

end Pss
