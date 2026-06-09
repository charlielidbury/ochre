import Pss.Syntax
import Pss.Star

/-!
# Algorithmic subtyping for System λ⊲

Figure 2 of Hutchins, *Pure Subtype Systems* (POPL 2010).

Subtyping is reformulated as an abstract reduction system with two kinds of
rewrite step (§6.1):

* **equivalence reduction** `t ≡→ t'` — β-steps (SRE-APP, guarded by the
  *transitive* subtyping premise `s ≤* t`) and `Top(t) ≡→ Top` (SRE-TOPAPP);
  applicable in any position not under a binder (`E≡`), and under binders
  via SR-FUN;
* **subtype reduction** `t ≤→ t'` — variable promotion (SRS-PROM) and
  promotion to `Top` (SRS-TOP); applicable only in *positive* positions:
  the left-hand side of applications (`E≤`) and function bodies (SR-FUN).

Then `Γ ⊢A t ≡ u` iff `t` and `u` join under `≡→`, and `Γ ⊢A t ≤ u` iff
`t ≤→* s *←≡ u` for some `s` (AS-REFL / AS-LEFT / AS-RIGHT), and `⊲*`
(AST-SUB / AST-TRANS) is the transitive closure used by the SRE-APP premise.

Everything is mutually inductive through the SRE-APP premise — exactly the
circularity the paper discusses in §6.2. Algorithmic subtyping is defined
over *all* terms, not just well-formed ones; contexts need only be
*prevalid* (P-CTX1 / P-CTX2).
-/
namespace Pss

/-- `Γ prevalid` (Figure 2): every bound is scoped within its context;
no well-formedness is required (§6.2). -/
inductive Prevalid : Ctx → Prop where
  /-- (P-CTX1). -/
  | nil : Prevalid []
  /-- `Γ prevalid, fv(t) ⊆ dom(Γ) ⟹ Γ, x ≤ t prevalid` (P-CTX2; the
  freshness premise `x ∉ dom(Γ)` is implicit in de Bruijn style). -/
  | cons {Γ : Ctx} {t : Term} :
      Prevalid Γ → Term.ClosedUnder Γ.length t → Prevalid (t :: Γ)

/-- Congruence contexts (Figure 2):

```
E≡ ::= [] | E≡(t) | t(E≡) | λx ≤ E≡. t
E≤ ::= [] | E≤(t)
```

indexed by the relation: `ECtx .eq` is `E≡` (any position not under a
binder — including the *bound* of a λ, which scopes outside the binder),
`ECtx .le` is `E≤` (positive positions only: left of application).
Function bodies are reached by SR-FUN, not by these contexts. -/
inductive ECtx : Rel → Type where
  | hole {r : Rel} : ECtx r
  | appL {r : Rel} : ECtx r → Term → ECtx r
  | appR : Term → ECtx .eq → ECtx .eq
  | lamBound : ECtx .eq → Term → ECtx .eq

/-- `E⊲[t]`: plug a term into a congruence context. No binder is crossed, so
this is plain structural replacement. -/
def ECtx.fill : {r : Rel} → ECtx r → Term → Term
  | _, .hole, s => s
  | _, .appL E t, s => .app (E.fill s) t
  | _, .appR t E, s => .app t (E.fill s)
  | _, .lamBound E t, s => .lam (E.fill s) t

mutual

/-- `Γ ⊢A t ⊲→ t'` (Figure 2): one step of subtype reduction (`r = .le`,
written `≤→`) or equivalence reduction (`r = .eq`, written `≡→`).

`SR-EQ` makes every `≡→` step an `≤→` step, so `Red Γ t .le t'` is the
relation written `≤→` in the paper and `Red Γ t .eq t'` is `≡→`. -/
inductive Red : Ctx → Term → Rel → Term → Prop where
  /-- `Γ prevalid, x ≤ t ∈ Γ ⟹ Γ ⊢A x ≤→ t` (SRS-PROM): variable promotion. -/
  | prom {Γ : Ctx} {x : Nat} {t : Term} :
      Prevalid Γ → Ctx.Bound Γ x t → Red Γ (.var x) .le t
  /-- `Γ prevalid ⟹ Γ ⊢A t ≤→ Top` (SRS-TOP): promotion to Top. -/
  | rtop {Γ : Ctx} {t : Term} : Prevalid Γ → Red Γ t .le .top
  /-- `Γ ⊢A s ≤* t ⟹ Γ ⊢A (λx ≤ t. u)(s) ≡→ [x ↦ s]u` (SRE-APP): guarded
  β-reduction. The premise uses transitive subtyping `≤*` — see §6.2 for why
  not plain `≤`. -/
  | beta {Γ : Ctx} {t u s : Term} :
      ATSub Γ s .le t → Red Γ (.app (.lam t u) s) .eq (u.subst1 s)
  /-- `Γ prevalid ⟹ Γ ⊢A Top(t) ≡→ Top` (SRE-TOPAPP): applications of Top
  collapse (needed because algorithmic subtyping ranges over ill-formed
  terms, §6.6.1). -/
  | topApp {Γ : Ctx} {t : Term} :
      Prevalid Γ → Red Γ (.app .top t) .eq .top
  /-- `Γ ⊢A t ⊲→ t' ⟹ Γ ⊢A E⊲[t] ⊲→ E⊲[t']` (SR-CONG). -/
  | cong {Γ : Ctx} {t t' : Term} {r : Rel} (E : ECtx r) :
      Red Γ t r t' → Red Γ (E.fill t) r (E.fill t')
  /-- `Γ, x ≤ t ⊢A u ⊲→ u' ⟹ Γ ⊢A λx ≤ t. u ⊲→ λx ≤ t. u'` (SR-FUN):
  reduction inside function bodies, under the extended context. -/
  | fn {Γ : Ctx} {t u u' : Term} {r : Rel} :
      Red (t :: Γ) u r u' → Red Γ (.lam t u) r (.lam t u')
  /-- `Γ ⊢A t ≡→ t' ⟹ Γ ⊢A t ≤→ t'` (SR-EQ): equivalence steps are subtype
  steps. -/
  | eq {Γ : Ctx} {t t' : Term} : Red Γ t .eq t' → Red Γ t .le t'

/-- `Γ ⊢A t ⊲ u` (Figure 2): algorithmic subtyping. `t ⊲ u` holds iff
`t ⊲→* s *←≡ u` for some `s` (cf. `Pss.Basic.asub_iff_join`). -/
inductive ASub : Ctx → Term → Rel → Term → Prop where
  /-- `Γ prevalid ⟹ Γ ⊢A t ⊲ t` (AS-REFL). -/
  | refl {Γ : Ctx} {t : Term} {r : Rel} : Prevalid Γ → ASub Γ t r t
  /-- `Γ ⊢A t ⊲→ t', t' ⊲ u ⟹ Γ ⊢A t ⊲ u` (AS-LEFT). -/
  | left {Γ : Ctx} {t t' u : Term} {r : Rel} :
      Red Γ t r t' → ASub Γ t' r u → ASub Γ t r u
  /-- `Γ ⊢A u ≡→ u', t ⊲ u' ⟹ Γ ⊢A t ⊲ u` (AS-RIGHT): the right-hand side
  may only be unfolded by equivalence steps. -/
  | right {Γ : Ctx} {t u u' : Term} {r : Rel} :
      Red Γ u .eq u' → ASub Γ t r u' → ASub Γ t r u

/-- `Γ ⊢A t ⊲* u` (Figure 2): transitive subtyping, the transitive closure
of `⊲`. This is the relation used in the SRE-APP premise. -/
inductive ATSub : Ctx → Term → Rel → Term → Prop where
  /-- `Γ ⊢A s ⊲ u ⟹ Γ ⊢A s ⊲* u` (AST-SUB). -/
  | sub {Γ : Ctx} {s u : Term} {r : Rel} : ASub Γ s r u → ATSub Γ s r u
  /-- `Γ ⊢A s ⊲* t, t ⊲* u ⟹ Γ ⊢A s ⊲* u` (AST-TRANS). -/
  | trans {Γ : Ctx} {s t u : Term} {r : Rel} :
      ATSub Γ s r t → ATSub Γ t r u → ATSub Γ s r u

end

/-- `Γ ⊢A t ⊲→* t'`: reduction sequences of `⊲→` (§6: written `⟶≡▸▸` / `⟶≤▸▸`). -/
abbrev RedStar (Γ : Ctx) (t : Term) (r : Rel) (t' : Term) : Prop :=
  Star (fun a b => Red Γ a r b) t t'

end Pss
