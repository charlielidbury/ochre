import Pss.Syntax

/-!
# Universes (§3.6) and the universe-aware application rule (§4.1)

Hutchins, *Pure Subtype Systems* (POPL 2010), §3.6 "Adding Universes" and the
§4.1 universe material ("Caveat: Pure Type Systems and Universes").

§3.6 extends the syntax of System λ⊲ with universe tags — `0` is the universe
of objects, `1` is the universe of types:

```
J, K    ::= 0 | 1
s, t, u ::= x^K | Top | λx^K ≤ t. u | t(u)
```

and defines the universe judgment `t ∈ U(K)` by the table

```
x^K          ∈ U(K)
Top          ∈ U(1)
λx^J ≤ t. u  ∈ U(K)   if u ∈ U(K)
t(u)         ∈ U(K)   if t ∈ U(K)
```

§4.1 (p. 292) modifies the well-formedness rule for application so that
function arguments are in the correct universe:

```
Γ ⊢ t ≤wf (λx^K ≤ s. Top),  u ≤wf s,  u ∈ U(K)
———————————————————————————————————————————————  (W-APP, modified)
Γ ⊢ t(u) wf
```

The paper presents universes "as a curiosity": *"The universe judgement shown
here is completely orthogonal to subtyping, so the presence or absence of
universes does not affect any of the results that we present in this paper."*
Accordingly this module is **standalone**: the Figure 1 mutual judgment block
is literally duplicated over tagged terms with only W-APP changed, and the
untagged system in `Pss.Declarative` is untouched. The text gives no other
rule changes, so duplication (rather than parametrizing the untagged system)
is the faithful encoding.

De Bruijn conventions (cf. `Pss.Syntax`):
* In the named syntax the tag is part of the variable's identity — §3.6:
  "Object variables are written as x⁰ or y⁰, while type variables are written
  as x¹ or y¹" — so `x⁰` and `x¹` are *distinct variables*. De Bruijn renders
  this by tagging each variable occurrence (`Tm.var x K`), each binder
  (`Tm.lam K t u` binds a `K`-tagged variable), and each context entry
  (`CtxT := List (Univ × Tm)`); `x^K ∈ dom(Γ)` becomes `CtxT.Dom Γ x K`.
* Substitutions are tag-indexed (`Nat → Univ → Tm`) so that the identity
  substitution is `Tm.var` and untouched occurrences keep their tags.
  `Tm.subst1` replaces de Bruijn index 0 *at every tag*; on terms whose
  index-0 occurrences are consistently tagged (the image of the named
  syntax, where a binder fixes its variable's tag) this is exactly the named
  `[x^K ↦ s]u`. Theorems carry that consistency premise explicitly
  (`Occurs`), keeping every statement honest on raw de Bruijn syntax.
-/

namespace Pss
namespace Universes

/-- Universe tags `J, K ::= 0 | 1` (§3.6): `zero` is the universe of objects,
`one` is the universe of types. -/
inductive Univ : Type where
  | zero
  | one
deriving Repr, DecidableEq

/-- Tagged terms `s, t, u ::= x^K | Top | λx^K ≤ t. u | t(u)` (§3.6).
`var x K` is `x^K`; `lam K t u` is `λx^K ≤ t. u` (the binder records the tag
of the variable it binds); `app t u` is `t(u)`. -/
inductive Tm : Type where
  | var : Nat → Univ → Tm
  | top : Tm
  | lam : Univ → Tm → Tm → Tm
  | app : Tm → Tm → Tm
deriving Repr, DecidableEq

namespace Tm

/-! ## Renaming and substitution (σ-calculus pattern of `Pss.Syntax`) -/

/-- Lift a renaming under one binder (`⇑ρ`). -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Apply a renaming to the free variables of a term; tags travel with their
occurrences. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | var x K => var (ρ x) K
  | top => top
  | lam K t u => lam K (t.rename ρ) (u.rename (liftRen ρ))
  | app t u => app (t.rename ρ) (u.rename ρ)

/-- Shift all free variables up by `d`. -/
def shift (t : Tm) (d : Nat := 1) : Tm := t.rename (· + d)

/-- Tagged substitutions map an occurrence `x^K` to `σ x K`; the identity
substitution is `var`. Cons: `(s .: σ) 0 K = s`, `(s .: σ) (n+1) K = σ n K`.
Index 0 is replaced at every tag — see the module docstring. -/
def scons (s : Tm) (σ : Nat → Univ → Tm) : Nat → Univ → Tm
  | 0, _ => s
  | n + 1, K => σ n K

/-- Lift a substitution under one binder (`⇑σ`). -/
def liftSubst (σ : Nat → Univ → Tm) : Nat → Univ → Tm
  | 0, K => var 0 K
  | n + 1, K => (σ n K).rename (· + 1)

/-- Apply a simultaneous substitution to the free variables of a term. -/
def subst (σ : Nat → Univ → Tm) : Tm → Tm
  | var x K => σ x K
  | top => top
  | lam K t u => lam K (t.subst σ) (u.subst (liftSubst σ))
  | app t u => app (t.subst σ) (u.subst σ)

/-- `[x ↦ s]u`: substitution of `s` for de Bruijn index 0 of `u`. -/
def subst1 (u s : Tm) : Tm := u.subst (scons s var)

end Tm

/-! ## The universe judgment (§3.6) -/

/-- `t ∈ U(K)` (§3.6), the four-line table verbatim. "Note that a function is
in universe K if its body is in K, regardless of what universe its argument
is in." -/
inductive InU : Tm → Univ → Prop where
  /-- `x^K ∈ U(K)`. -/
  | var {x : Nat} {K : Univ} : InU (.var x K) K
  /-- `Top ∈ U(1)`. -/
  | top : InU .top .one
  /-- `λx^J ≤ t. u ∈ U(K)` if `u ∈ U(K)`. -/
  | lam {J K : Univ} {t u : Tm} : InU u K → InU (.lam J t u) K
  /-- `t(u) ∈ U(K)` if `t ∈ U(K)`. -/
  | app {K : Univ} {t u : Tm} : InU t K → InU (.app t u) K

/-- The judgment "determines whether a term t is an object or a type" (§3.6):
a term inhabits at most one universe. -/
theorem InU.unique {t : Tm} {J : Univ} (h₁ : InU t J) :
    ∀ {K : Univ}, InU t K → J = K := by
  induction h₁ with
  | var => intro K h₂; cases h₂; rfl
  | top => intro K h₂; cases h₂; rfl
  | lam h ih => intro K h₂; cases h₂ with | lam h₂ => exact ih h₂
  | app h ih => intro K h₂; cases h₂ with | app h₂ => exact ih h₂

/-- Every tagged term inhabits a universe (the head of its spine is a tagged
variable or `Top`, both of which the §3.6 table covers). -/
theorem InU.total : ∀ t : Tm, ∃ K, InU t K := by
  intro t
  induction t with
  | var x K => exact ⟨K, .var⟩
  | top => exact ⟨.one, .top⟩
  | lam J t u iht ihu => obtain ⟨K, h⟩ := ihu; exact ⟨K, .lam h⟩
  | app t u iht ihu => obtain ⟨K, h⟩ := iht; exact ⟨K, .app h⟩

/-- Renaming preserves universes: tags travel with occurrences. -/
theorem InU.rename {t : Tm} {K : Univ} (h : InU t K) (ρ : Nat → Nat) :
    InU (t.rename ρ) K := by
  induction h generalizing ρ with
  | var => exact .var
  | top => exact .top
  | lam h ih => exact .lam (ih (Tm.liftRen ρ))
  | app h ih => exact .app (ih ρ)

/-! ## Universes are preserved under β-substitution (§4.1)

> "It is easy to see that universes are preserved under β-reduction, because
> a variable in universe K is replaced with a term in universe K."

The honest de Bruijn statement needs to say *which* occurrences are
"a variable in universe K": `Occurs x K t` records that the tagged variable
`x^K` occurs free in `t`, so "the substituted variable is K-tagged" is the
premise that every index-0 occurrence carries tag `K` — automatic in the
named syntax, where the binder fixes its variable's tag. -/

/-- The tagged variable `x^K` occurs free in `t` (binders shift the index,
as in Figure 1's `fv(t)`). -/
inductive Occurs : Nat → Univ → Tm → Prop where
  | var {x : Nat} {K : Univ} : Occurs x K (.var x K)
  | lamBound {x : Nat} {K J : Univ} {t u : Tm} :
      Occurs x K t → Occurs x K (.lam J t u)
  | lamBody {x : Nat} {K J : Univ} {t u : Tm} :
      Occurs (x + 1) K u → Occurs x K (.lam J t u)
  | appL {x : Nat} {K : Univ} {t u : Tm} :
      Occurs x K t → Occurs x K (.app t u)
  | appR {x : Nat} {K : Univ} {t u : Tm} :
      Occurs x K u → Occurs x K (.app t u)

/-- Substitution preserves universes, provided the substitution respects the
universe of every occurrence it replaces (§4.1: "a variable in universe K is
replaced with a term in universe K"). -/
theorem InU.subst {t : Tm} {J : Univ} (h : InU t J) :
    ∀ σ : Nat → Univ → Tm,
      (∀ (x : Nat) (K : Univ), Occurs x K t → InU (σ x K) K) →
      InU (t.subst σ) J := by
  induction h with
  | var => intro σ hσ; exact hσ _ _ .var
  | top => intro σ hσ; exact .top
  | lam h ih =>
    intro σ hσ
    refine .lam (ih (Tm.liftSubst σ) ?_)
    intro x K hocc
    cases x with
    | zero => exact .var
    | succ x => exact (hσ x K (.lamBody hocc)).rename (· + 1)
  | app h ih =>
    intro σ hσ
    exact .app (ih σ fun x K hocc => hσ x K (.appL hocc))

/-- **Universes are preserved under β-substitution** (§4.1, p. 292):
substituting a `U(K)` term `s` for a `K`-tagged variable (de Bruijn index 0,
all of whose occurrences carry tag `K`) preserves membership in `U(J)`. -/
theorem subst1_preserves {u s : Tm} {J K : Univ} (hs : InU s K)
    (htag : ∀ K' : Univ, Occurs 0 K' u → K' = K) (hu : InU u J) :
    InU (u.subst1 s) J := by
  refine hu.subst _ ?_
  intro x K' hocc
  cases x with
  | zero =>
    have hK : K' = K := htag K' hocc
    subst hK
    exact hs
  | succ x => exact .var

/-- The β-redex form of `subst1_preserves`: contracting
`(λx^K ≤ t. u)(s) ⟶ [x ↦ s]u` preserves `∈ U(J)` whenever the argument is
in the binder's universe — exactly the premise the modified W-APP rule
guarantees for well-formed redexes. -/
theorem beta_preserves {t u s : Tm} {J K : Univ} (hs : InU s K)
    (htag : ∀ K' : Univ, Occurs 0 K' u → K' = K)
    (h : InU (.app (.lam K t u) s) J) : InU (u.subst1 s) J := by
  cases h with
  | app h =>
    cases h with
    | lam h => exact subst1_preserves hs htag h

/-! ## Tagged contexts -/

/-- Tagged type contexts `Γ ::= ∅ | Γ, x^K ≤ t` (Figure 1 over §3.6 syntax):
a named context entry binds a *tagged* variable, so the de Bruijn entry
records the tag alongside the bound. Conventions as `Pss.Ctx`. -/
abbrev CtxT := List (Univ × Tm)

namespace CtxT

/-- `x^K ∈ dom(Γ)` (Figure 1, Notation): the tagged variable `x^K` is bound
in `Γ`. The untagged `x ∈ dom(Γ)` of W-VAR becomes tag-aware because the
domain of a named tagged context consists of tagged variables. -/
inductive Dom : CtxT → Nat → Univ → Prop where
  | here {Γ : CtxT} {K : Univ} {t : Tm} : Dom ((K, t) :: Γ) 0 K
  | there {Γ : CtxT} {K K' : Univ} {t : Tm} {x : Nat} :
      Dom Γ x K → Dom ((K', t) :: Γ) (x + 1) K

/-- `x^K ≤ t ∈ Γ` (Figure 1, Notation): the bound is shifted into
whole-context scope exactly as `Pss.Ctx.Bound`. -/
inductive Bound : CtxT → Nat → Univ → Tm → Prop where
  | here {Γ : CtxT} {K : Univ} {t : Tm} : Bound ((K, t) :: Γ) 0 K (t.shift 1)
  | there {Γ : CtxT} {K K' : Univ} {u t : Tm} {x : Nat} :
      Bound Γ x K t → Bound ((K', u) :: Γ) (x + 1) K (t.shift 1)

end CtxT

/-! ## The Figure 1 judgment block over tagged terms, with W-APP modified

A literal duplicate of `Pss.Declarative` (`CtxWf / Wf / WellSub / Sub`,
Figure 1) over tagged syntax. The **only** rule that differs from Figure 1
is W-APP, which gains the `u ∈ U(K)` premise of §4.1. Rules that mention a
bound variable (`W-GAM2`, `W-FUN`, `DS-FUN`, `DS-VAR`, `DS-EVAR`) thread the
variable's tag; in the named syntax both occurrences of `x` in such a rule
are the same tagged variable, so e.g. DS-FUN relates `λx^K ≤ t. u` and
`λx^K ≤ t'. u'` with a shared `K`. The metavariable `⊲` is `Pss.Rel`. -/

mutual

/-- `Γ wf` — context well-formedness (Figure 1, W-GAM1/W-GAM2; tags carried,
rules unchanged). -/
inductive CtxWfT : CtxT → Prop where
  /-- `∅ wf` (W-GAM1). -/
  | nil : CtxWfT []
  /-- `Γ wf, Γ ⊢ t wf ⟹ Γ, x^K ≤ t wf` (W-GAM2). -/
  | cons {Γ : CtxT} {K : Univ} {t : Tm} :
      CtxWfT Γ → WfT Γ t → CtxWfT ((K, t) :: Γ)

/-- `Γ ⊢ t wf` — well-formedness (Figure 1) with the §4.1 W-APP. -/
inductive WfT : CtxT → Tm → Prop where
  /-- `Γ wf, x^K ∈ dom(Γ) ⟹ Γ ⊢ x^K wf` (W-VAR). -/
  | var {Γ : CtxT} {x : Nat} {K : Univ} :
      CtxWfT Γ → CtxT.Dom Γ x K → WfT Γ (.var x K)
  /-- `Γ wf ⟹ Γ ⊢ Top wf` (W-TOP). -/
  | top {Γ : CtxT} : CtxWfT Γ → WfT Γ .top
  /-- `Γ, x^K ≤ t ⊢ u wf ⟹ Γ ⊢ λx^K ≤ t. u wf` (W-FUN). -/
  | fn {Γ : CtxT} {K : Univ} {t u : Tm} :
      WfT ((K, t) :: Γ) u → WfT Γ (.lam K t u)
  /-- `Γ ⊢ t ≤wf (λx^K ≤ s. Top), Γ ⊢ u ≤wf s, u ∈ U(K) ⟹ Γ ⊢ t(u) wf`
  (**W-APP, modified** — §4.1, p. 292: "The well-formedness rule for function
  application must also be modified to ensure that function arguments are in
  the correct universe"). -/
  | app {Γ : CtxT} {K : Univ} {t u s : Tm} :
      WellSubT Γ t .le (.lam K s .top) → WellSubT Γ u .le s → InU u K →
      WfT Γ (.app t u)

/-- `Γ ⊢ t ⊲wf u` — well-subtyping (Figure 1, W-SUB; unchanged). -/
inductive WellSubT : CtxT → Tm → Rel → Tm → Prop where
  /-- `Γ ⊢ t wf, u wf, Γ ⊢ t ⊲ u ⟹ Γ ⊢ t ⊲wf u` (W-SUB). -/
  | sub {Γ : CtxT} {t u : Tm} {r : Rel} :
      WfT Γ t → WfT Γ u → SubT Γ t r u → WellSubT Γ t r u

/-- `Γ ⊢ t ⊲ u` — declarative subtyping (Figure 1, DS-rules; unchanged —
"the subtype relation is still defined over all terms in all universes. In
particular, subtyping can cross universe boundaries"). -/
inductive SubT : CtxT → Tm → Rel → Tm → Prop where
  /-- (DS-TRANS). -/
  | trans {Γ : CtxT} {s t u : Tm} {r : Rel} :
      SubT Γ s r t → SubT Γ t r u → WfT Γ t → SubT Γ s r u
  /-- (DS-SYM). -/
  | symm {Γ : CtxT} {t u : Tm} : SubT Γ u .eq t → SubT Γ t .eq u
  /-- (DS-EQ). -/
  | eq {Γ : CtxT} {t u : Tm} : SubT Γ t .eq u → SubT Γ t .le u
  /-- `Γ ⊢ x^K ≡ x^K` (DS-VAR). -/
  | var {Γ : CtxT} {x : Nat} {K : Univ} : SubT Γ (.var x K) .eq (.var x K)
  /-- (DS-TOP). -/
  | top {Γ : CtxT} : SubT Γ .top .eq .top
  /-- (DS-FUN); both sides bind the same tagged variable `x^K`. -/
  | fn {Γ : CtxT} {K : Univ} {t t' u u' : Tm} {r : Rel} :
      SubT Γ t .eq t' → SubT ((K, t) :: Γ) u r u' →
      SubT Γ (.lam K t u) r (.lam K t' u')
  /-- (DS-APP). -/
  | app {Γ : CtxT} {t t' u u' : Tm} {r : Rel} :
      SubT Γ t r t' → SubT Γ u .eq u' → SubT Γ (.app t u) r (.app t' u')
  /-- `Γ ⊢ (λx^K ≤ t. u)(s) ≡ [x ↦ s]u` (DS-EAPP). -/
  | eapp {Γ : CtxT} {K : Univ} {t u s : Tm} :
      SubT Γ (.app (.lam K t u) s) .eq (u.subst1 s)
  /-- (DS-ETOP). -/
  | etop {Γ : CtxT} {t : Tm} : SubT Γ t .le .top
  /-- `x^K ≤ t ∈ Γ ⟹ Γ ⊢ x^K ≤ t` (DS-EVAR). -/
  | evar {Γ : CtxT} {x : Nat} {K : Univ} {t : Tm} :
      CtxT.Bound Γ x K t → SubT Γ (.var x K) .le t

end

/-! ## Reduction over tagged terms (Figure 1) -/

/-- One-hole contexts over tagged terms (Figure 1, Notation; cf.
`Pss.TermCtx`). -/
inductive TermCtxT : Type where
  | hole : TermCtxT
  | appL : TermCtxT → Tm → TermCtxT
  | appR : Tm → TermCtxT → TermCtxT
  | lamBound : Univ → TermCtxT → Tm → TermCtxT
  | lamBody : Univ → Tm → TermCtxT → TermCtxT

/-- `C[t]`: capture-permitting replacement, as in `Pss.TermCtx.fill`. -/
def TermCtxT.fill : TermCtxT → Tm → Tm
  | .hole, s => s
  | .appL C t, s => .app (C.fill s) t
  | .appR t C, s => .app t (C.fill s)
  | .lamBound K C t, s => .lam K (C.fill s) t
  | .lamBody K t C, s => .lam K t (C.fill s)

/-- `t ⟶ t'` over tagged terms (Figure 1, E-APP / E-CONG), used to state the
§4.1 preservation remark. -/
inductive StepT : Tm → Tm → Prop where
  /-- `(λx^K ≤ t. u)(s) ⟶ [x ↦ s]u` (E-APP). -/
  | eapp {K : Univ} {t u s : Tm} : StepT (.app (.lam K t u) s) (u.subst1 s)
  /-- `t ⟶ t' ⟹ C[t] ⟶ C[t']` (E-CONG). -/
  | econg {t t' : Tm} (C : TermCtxT) : StepT t t' → StepT (C.fill t) (C.fill t')

/-! ## The §4.1 examples: tagged `Nat` and `3`

> "Moreover, by extending our definitions of 3 and Nat with universe tags,
> it also clear that 3 is an object (i.e. 3 ∈ U(0)), and Nat is a type:
>
>   Nat = λx¹ ≤ Top. λf⁰ ≤ (x¹ → x¹). λa⁰ ≤ x¹. x¹
>   3   = λx¹ ≤ Top. λf⁰ ≤ (x¹ → x¹). λa⁰ ≤ x¹. f⁰(f⁰(f⁰(a⁰)))"
-/

/-- The §3.5 arrow sugar `t → u := λy ≤ t. u` (`y` fresh) over tagged syntax.
The paper leaves the tag of the fresh `y` implicit; the universe judgment is
insensitive to binder tags (the λ-line of the §3.6 table constrains only the
body), so any choice yields the same `∈ U(K)` facts. We tag `y` with `K`,
instantiated to `0` below: for `f⁰(a⁰)` to be well-formed under the modified
W-APP, `f`'s bound `x¹ → x¹` must promote to a `λy^K ≤ s. Top` whose tag `K`
is the universe of the argument `a⁰ ∈ U(0)`, and DS-FUN preserves binder
tags — so the sugar variable of `x¹ → x¹` must be `y⁰`. -/
def arrowT (K : Univ) (t u : Tm) : Tm := .lam K t (u.shift 1)

/-- `Nat = λx¹ ≤ Top. λf⁰ ≤ (x¹ → x¹). λa⁰ ≤ x¹. x¹` (§4.1, p. 292). -/
def NatT : Tm :=
  .lam .one .top
    (.lam .zero (arrowT .zero (.var 0 .one) (.var 0 .one))
      (.lam .zero (.var 1 .one)
        (.var 2 .one)))

/-- `3 = λx¹ ≤ Top. λf⁰ ≤ (x¹ → x¹). λa⁰ ≤ x¹. f⁰(f⁰(f⁰(a⁰)))` (§4.1). -/
def ThreeT : Tm :=
  .lam .one .top
    (.lam .zero (arrowT .zero (.var 0 .one) (.var 0 .one))
      (.lam .zero (.var 1 .one)
        (.app (.var 1 .zero)
          (.app (.var 1 .zero)
            (.app (.var 1 .zero) (.var 0 .zero))))))

/-- `Nat ∈ U(1)` — "Nat is a type" (§4.1): the body spine ends at `x¹`. -/
theorem NatT_in_U1 : InU NatT .one := .lam (.lam (.lam .var))

/-- `3 ∈ U(0)` — "3 is an object" (§4.1): the body spine ends at the head
`f⁰` of `f⁰(f⁰(f⁰(a⁰)))`. -/
theorem ThreeT_in_U0 : InU ThreeT .zero := .lam (.lam (.lam (.app .var)))

end Universes

namespace Statements

/-- §4.1 (p. 292): *"It is easy to see that universes are preserved under
β-reduction, because a variable in universe K is replaced with a term in
universe K."* Stated for well-formed terms — the modified W-APP rule is what
guarantees that the argument of a redex lies in the binder's universe.

Status: asserted without proof in the paper (sketch above; details in the
author's PhD thesis [19]). The substitution core is mechanized here as
`Pss.Universes.subst1_preserves` / `Pss.Universes.beta_preserves`.
Mechanization of this full statement is incomplete: extracting `InU s K` for
a redex argument from `WfT` requires inversion of well-subtyping
(Lemma 5.2 of the paper, which rests on transitivity elimination,
Conjecture 5.1 — open), and the E-CONG cases additionally need the
binder-consistency invariant of well-formed terms (every variable occurrence
tagged like its binder, enforced through W-VAR/W-FUN). -/
def universes_preserved_under_reduction : Prop :=
  ∀ (Γ : Universes.CtxT) (t t' : Universes.Tm) (J : Universes.Univ),
    Universes.WfT Γ t → Universes.InU t J → Universes.StepT t t' →
    Universes.InU t' J

end Statements

end Pss
