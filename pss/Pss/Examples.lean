import Pss.Basic

/-!
# §3.5 Example: 3 ≤ Nat

Hutchins, *Pure Subtype Systems* (POPL 2010), §3.5 and §3.5.1.

The standard Church encodings in System λ⊲:

```
Nat = λx ≤ Top. (x → x) → x → x
3   = λx ≤ Top. λf ≤ (x → x). λa ≤ x. f(f(f(a)))
```

and the paper's derivation that `3 ≤ Nat`, mechanized three ways:
declaratively (`Sub`, Figure 1), well-formedly (`WellSub`, §3.4), and
algorithmically (`ASub`, Figure 2). The crux (§3.5) is, in the context
`Γ₃ = x ≤ Top, f ≤ (λy ≤ x. x), a ≤ x`:

```
Γ₃ ⊢ f(f(f(a))) ≤ (λy ≤ x. x)(f(f(a)))   by DS-EVAR
              ≡ x                          by DS-EAPP
```

§3.5.1 is the abstract-interpretation example: with Church-style addition,
`Nat + 3 ≡ Nat` holds algorithmically (`nat_plus_three_eq_nat`).

De Bruijn conventions (cf. `Pss.Syntax`): contexts list the innermost
binding first, so in `Γ₃` we have `a = var 0`, `f = var 1`, `x = var 2`,
and `Ctx.Bound` produces bounds shifted into whole-context scope.
-/

namespace Pss.Examples

/-- `Nat = λx ≤ Top. (x → x) → x → x` (§3.5), via the §3 arrow sugar. -/
def nat : Term :=
  .lam .top (Term.arrow (Term.arrow (.var 0) (.var 0)) (Term.arrow (.var 0) (.var 0)))

/-- `3 = λx ≤ Top. λf ≤ (x → x). λa ≤ x. f(f(f(a)))` (§3.5). -/
def three : Term :=
  .lam .top (.lam (Term.arrow (.var 0) (.var 0))
    (.lam (.var 1) (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0))))))

example : nat = .lam .top (.lam (.lam (.var 0) (.var 1)) (.lam (.var 1) (.var 2))) := rfl

example : three =
    .lam .top (.lam (.lam (.var 0) (.var 1))
      (.lam (.var 1) (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))))) := rfl

/-- `Γ₃ = x ≤ Top, f ≤ (λy ≤ x. x), a ≤ x` (§3.5), innermost binding first;
each bound is scoped in the tail of the list. -/
def Γ₃ : Ctx := [.var 1, .lam (.var 0) (.var 1), .top]

/-- `a ≤ x ∈ Γ₃`: the stored bound `var 1` is shifted into whole-context
scope, where `x = var 2` (Figure 1 Notation, de Bruijn form). -/
private theorem bound_a : Ctx.Bound Γ₃ 0 (.var 2) := .here

/-- `f ≤ (λy ≤ x. x) ∈ Γ₃`, the bound shifted into whole-context scope. -/
private theorem bound_f : Ctx.Bound Γ₃ 1 (.lam (.var 2) (.var 3)) := .there .here

/-- `x ≤ Top ∈ Γ₃`. -/
private theorem bound_x : Ctx.Bound Γ₃ 2 .top := .there (.there .here)

/-! ## Well-formedness of Γ₃ (Figure 1: W-GAM1, W-GAM2, W-VAR, W-TOP, W-FUN) -/

private theorem ctxWf_top : CtxWf [.top] := .cons .nil (.top .nil)

private theorem ctxWf_Γ₂ : CtxWf [.lam (.var 0) (.var 1), .top] :=
  .cons ctxWf_top
    (.fn (.var (.cons ctxWf_top (.var ctxWf_top (by decide))) (by decide)))

/-- `Γ₃ wf` (W-GAM2 stacked on W-GAM1). -/
private theorem ctxWf_Γ₃ : CtxWf Γ₃ :=
  .cons ctxWf_Γ₂ (.var ctxWf_Γ₂ (by decide))

private theorem wf_a : Wf Γ₃ (.var 0) := .var ctxWf_Γ₃ (by decide)
private theorem wf_f : Wf Γ₃ (.var 1) := .var ctxWf_Γ₃ (by decide)
private theorem wf_x : Wf Γ₃ (.var 2) := .var ctxWf_Γ₃ (by decide)

private theorem ctxWf_xΓ₃ : CtxWf (.var 2 :: Γ₃) := .cons ctxWf_Γ₃ wf_x

/-- `Γ₃ ⊢ (λy ≤ x. x) wf` (W-FUN, W-VAR) — `f`'s bound in `Γ₃` scope. -/
private theorem wf_idx : Wf Γ₃ (.lam (.var 2) (.var 3)) :=
  .fn (.var ctxWf_xΓ₃ (by decide))

/-- `Γ₃ ⊢ (λy ≤ x. Top) wf` (W-FUN, W-TOP) — the function bound used by W-APP. -/
private theorem wf_xtop : Wf Γ₃ (.lam (.var 2) .top) := .fn (.top ctxWf_xΓ₃)

/-! ## Well-subtyping helpers (W-SUB, §3.4) -/

private theorem wf_of_wellSub {Γ : Ctx} {t u : Term} {r : Rel}
    (h : WellSub Γ t r u) : Wf Γ t := by
  cases h with | sub h _ _ => exact h

private theorem sub_of_wellSub {Γ : Ctx} {t u : Term} {r : Rel}
    (h : WellSub Γ t r u) : Sub Γ t r u := by
  cases h with | sub _ _ h => exact h

/-- `Γ₃ ⊢ (λy ≤ x. x) ≤wf (λy ≤ x. Top)` (DS-FUN with DS-VAR / DS-ETOP). -/
private theorem idx_le_xtop :
    WellSub Γ₃ (.lam (.var 2) (.var 3)) .le (.lam (.var 2) .top) :=
  .sub wf_idx wf_xtop (.fn .var .etop)

/-- `Γ₃ ⊢ f ≤wf (λy ≤ x. Top)`: DS-EVAR promotes `f` to its bound
`λy ≤ x. x`, DS-TRANS glues through that (well-formed) middle term. -/
private theorem f_le_xtop : WellSub Γ₃ (.var 1) .le (.lam (.var 2) .top) :=
  .sub wf_f wf_xtop (.trans (.evar bound_f) (.fn .var .etop) wf_idx)

/-- `Γ₃ ⊢ a ≤wf x` (DS-EVAR, W-SUB). -/
private theorem a_le_x : WellSub Γ₃ (.var 0) .le (.var 2) :=
  .sub wf_a wf_x (.evar bound_a)

/-- The §3.5 step: from `Γ₃ ⊢ t ≤wf x` derive `Γ₃ ⊢ f(t) ≤wf x`.
DS-EVAR promotes `f` under DS-APP, DS-EAPP β-contracts
`(λy ≤ x. x)(t) ≡ x`, and DS-TRANS glues them through the middle term
`(λy ≤ x. x)(t)`, whose well-formedness is W-APP with `t ≤wf x` and
`(λy ≤ x. x) ≤wf (λy ≤ x. Top)`. -/
private theorem app_f_le_x {t : Term} (h : WellSub Γ₃ t .le (.var 2)) :
    WellSub Γ₃ (.app (.var 1) t) .le (.var 2) :=
  have wf_mid : Wf Γ₃ (.app (.lam (.var 2) (.var 3)) t) := .app idx_le_xtop h
  have h₁ : Sub Γ₃ (.app (.var 1) t) .le (.app (.lam (.var 2) (.var 3)) t) :=
    .app (.evar bound_f) (Sub.refl_eq t Γ₃)
  have h₂ : Sub Γ₃ (.app (.lam (.var 2) (.var 3)) t) .le (.var 2) := .eq .eapp
  .sub (.app f_le_xtop h) wf_x (.trans h₁ h₂ wf_mid)

/-- `Γ₃ ⊢ f(a) ≤wf x` (§3.5). -/
private theorem fa_le_x : WellSub Γ₃ (.app (.var 1) (.var 0)) .le (.var 2) :=
  app_f_le_x a_le_x

/-- `Γ₃ ⊢ f(f(a)) ≤wf x` (§3.5). -/
private theorem ffa_le_x :
    WellSub Γ₃ (.app (.var 1) (.app (.var 1) (.var 0))) .le (.var 2) :=
  app_f_le_x fa_le_x

/-- `Γ₃ ⊢ f(f(f(a))) ≤wf x` (§3.5). -/
private theorem fffa_le_x :
    WellSub Γ₃ (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))) .le
      (.var 2) :=
  app_f_le_x ffa_le_x

/-- §3.5, the paper's key derivation:
`Γ, f ≤ (λy ≤ x. x), a ≤ x ⊢ f(f(f(a))) ≤ x` by DS-EVAR then DS-EAPP,
glued by DS-TRANS. -/
theorem fff_le_x :
    Sub Γ₃ (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))) .le
      (.var 2) :=
  sub_of_wellSub fffa_le_x

/-- §3.5: `⊢ 3 ≤ Nat` (declarative). DS-FUN three times — each extends the
context with the *left* bound, yielding exactly `Γ₃` — down to `fff_le_x`. -/
theorem three_le_nat : Sub [] three .le nat :=
  .fn .top (.fn (Sub.refl_eq _ _) (.fn .var fff_le_x))

/-- `⊢ Nat wf` (W-FUN stacked; the body `x` is W-VAR in `Γ₃`). -/
private theorem wf_nat : Wf [] nat :=
  .fn (.fn (.fn (.var ctxWf_Γ₃ (by decide))))

/-- `⊢ 3 wf` (W-FUN stacked on the W-APP derivation inside `fffa_le_x`). -/
private theorem wf_three : Wf [] three :=
  .fn (.fn (.fn (wf_of_wellSub fffa_le_x)))

/-- §3.5: `⊢ 3 ≤wf Nat` (W-SUB, §3.4). -/
theorem three_le_nat_wf : WellSub [] three .le nat :=
  .sub wf_three wf_nat three_le_nat

/-! ## §3.5 algorithmically (Figure 2)

`3 ≤ Nat` as a join: `3`'s body reduces under SR-FUN — SRS-PROM promotes
`f` inside `E≤ = [](t)`, then SRE-APP β-contracts, guarded by the
transitive-subtyping premise `t ≤* x` built recursively the same way. -/

/-- `Γ₃ prevalid` (P-CTX1, P-CTX2). -/
private theorem prevalid_Γ₃ : Prevalid Γ₃ :=
  .cons (.cons (.cons .nil .top) (.lam (.var (by decide)) (.var (by decide))))
    (.var (by decide))

/-- `Γ₃ ⊢A a ≤* x`: one SRS-PROM step, joined with reflexivity (AST-SUB). -/
private theorem atsub_a_le_x : ATSub Γ₃ (.var 0) .le (.var 2) :=
  .sub (ASub.of_join prevalid_Γ₃ (.single (.prom prevalid_Γ₃ bound_a)) .refl)

/-- `Γ₃ ⊢A f ≤* (λy ≤ x. x)`: one SRS-PROM step (AST-SUB). -/
private theorem atsub_f_le_idx : ATSub Γ₃ (.var 1) .le (.lam (.var 2) (.var 3)) :=
  .sub (ASub.of_join prevalid_Γ₃ (.single (.prom prevalid_Γ₃ bound_f)) .refl)

/-- `Γ₃ ⊢A x ≤* Top`: one SRS-TOP step (AST-SUB). -/
private theorem atsub_x_le_top : ATSub Γ₃ (.var 2) .le .top :=
  .sub (ASub.of_join prevalid_Γ₃ (.single (.rtop prevalid_Γ₃)) .refl)

/-- The §3.5 step as subtype reduction: given `Γ₃ ⊢A t ≤* x`,
`f(t) ≤→ (λy ≤ x. x)(t)` by SRS-PROM inside `E≤ = [](t)` (SR-CONG), then
`≡→ x` by SRE-APP (lifted by SR-EQ). -/
private theorem redstar_app_f {t : Term} (h : ATSub Γ₃ t .le (.var 2)) :
    RedStar Γ₃ (.app (.var 1) t) .le (.var 2) :=
  .head (.cong (.appL .hole t) (.prom prevalid_Γ₃ bound_f))
    (.single (.eq (.beta h)))

/-- `Γ₃ ⊢A f(t) ≤* x` from `Γ₃ ⊢A t ≤* x` (join + AST-SUB). -/
private theorem atsub_app_f {t : Term} (h : ATSub Γ₃ t .le (.var 2)) :
    ATSub Γ₃ (.app (.var 1) t) .le (.var 2) :=
  .sub (ASub.of_join prevalid_Γ₃ (redstar_app_f h) .refl)

/-- `Γ₃ ⊢A f(f(f(a))) ≤* x` (§3.5, algorithmic). -/
private theorem atsub_fffa :
    ATSub Γ₃ (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))) .le
      (.var 2) :=
  atsub_app_f (atsub_app_f (atsub_app_f atsub_a_le_x))

/-- `Γ₃ ⊢A f(f(f(a))) ≤→* x` (§3.5, algorithmic). -/
private theorem redstar_fffa :
    RedStar Γ₃ (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))) .le
      (.var 2) :=
  redstar_app_f (atsub_app_f (atsub_app_f atsub_a_le_x))

/-- §3.5: `⊢A 3 ≤ Nat` (algorithmic): the body join lifted through three
SR-FUN steps, with `Nat` already in normal form (AS-REFL on the right). -/
theorem three_le_nat_alg : ASub [] three .le nat :=
  ASub.of_join .nil (RedStar.fn (RedStar.fn (RedStar.fn redstar_fffa))) .refl

/-! ## §3.5.1 Singleton types and abstract interpretation: Nat + 3 ≡ Nat

Church-style addition. Evaluating `add(Nat)(3)` β-reduces (each SRE-APP
guarded by an algorithmic subtype check, e.g. `3 ≤* Nat` itself) to `Nat`'s
normal form — abstract interpretation with the type `Nat` used as a value. -/

/-- `add = λm ≤ Nat. λn ≤ Nat. λx ≤ Top. λf ≤ (x → x). λa ≤ x.
m(x)(f)(n(x)(f)(a))` — Church addition in System λ⊲ (§3.5.1). `Nat` is
closed, so its shift under the `m` binder is itself. -/
def add : Term :=
  .lam nat (.lam nat (.lam .top (.lam (Term.arrow (.var 0) (.var 0))
    (.lam (.var 1)
      (.app (.app (.app (.var 4) (.var 2)) (.var 1))
        (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0)))))))

example : nat.shift 1 = nat := rfl

/-- `[m ↦ Nat]` applied to `add`'s outer body: the first SRE-APP contractum
of `add(Nat)(3)`. -/
private def add₁ : Term :=
  .lam nat (.lam .top (.lam (.lam (.var 0) (.var 1))
    (.lam (.var 1)
      (.app (.app (.app nat (.var 2)) (.var 1))
        (.app (.app (.app (.var 3) (.var 2)) (.var 1)) (.var 0))))))

/-- `[n ↦ 3]` applied next: `λx ≤ Top. λf ≤ (x → x). λa ≤ x.
Nat(x)(f)(3(x)(f)(a))`. -/
private def addBody : Term :=
  .lam .top (.lam (.lam (.var 0) (.var 1))
    (.lam (.var 1)
      (.app (.app (.app nat (.var 2)) (.var 1))
        (.app (.app (.app three (.var 2)) (.var 1)) (.var 0)))))

/-- `⊢A Nat ≤* Nat` (AS-REFL, AST-SUB): the check guarding `add(Nat)`. -/
private theorem atsub_nat_le_nat : ATSub [] nat .le nat := .sub (.refl .nil)

/-- `⊢A 3 ≤* Nat`: the check guarding `add(Nat)(3)` — §3.5's result reused
as the SRE-APP premise. -/
private theorem atsub_three_le_nat : ATSub [] three .le nat :=
  .sub three_le_nat_alg

/-- `3(x)(f)(a)` in `Γ₃` scope. -/
private def arg3 : Term := .app (.app (.app three (.var 2)) (.var 1)) (.var 0)

/-- `Nat(x)`'s SRE-APP contractum: `(λg ≤ (x → x). x → x)` in `Γ₃` scope. -/
private def natX : Term := .lam (.lam (.var 2) (.var 3)) (.lam (.var 3) (.var 4))

/-- `Nat(x)(f)`'s contractum: `λy ≤ x. x` in `Γ₃` scope. -/
private def idx : Term := .lam (.var 2) (.var 3)

/-- `3(x)`'s contractum: `λf' ≤ (x → x). λa' ≤ x. f'(f'(f'(a')))`. -/
private def threeX : Term :=
  .lam (.lam (.var 2) (.var 3))
    (.lam (.var 3) (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))))

/-- `3(x)(f)`'s contractum: `λa' ≤ x. f(f(f(a')))`. -/
private def threeXF : Term :=
  .lam (.var 2) (.app (.var 2) (.app (.var 2) (.app (.var 2) (.var 0))))

/-- `Γ₃ ⊢A Nat(x)(f)(3(x)(f)(a)) ≡→* x` (§3.5.1): six SRE-APP steps, each
guarded by the appropriate `≤*` premise, placed by SR-CONG in `E≡`. -/
private theorem redstar_add_body :
    RedStar Γ₃
      (.app (.app (.app nat (.var 2)) (.var 1))
        (.app (.app (.app three (.var 2)) (.var 1)) (.var 0)))
      .eq (.var 2) :=
  have s₁ : Red Γ₃
      (.app (.app (.app nat (.var 2)) (.var 1)) arg3)
      .eq (.app (.app natX (.var 1)) arg3) :=
    .cong (.appL (.appL .hole (.var 1)) arg3) (.beta atsub_x_le_top)
  have s₂ : Red Γ₃ (.app (.app natX (.var 1)) arg3) .eq (.app idx arg3) :=
    .cong (.appL .hole arg3) (.beta atsub_f_le_idx)
  have s₃ : Red Γ₃ (.app idx arg3) .eq
      (.app idx (.app (.app threeX (.var 1)) (.var 0))) :=
    .cong (.appR idx (.appL (.appL .hole (.var 1)) (.var 0)))
      (.beta atsub_x_le_top)
  have s₄ : Red Γ₃ (.app idx (.app (.app threeX (.var 1)) (.var 0))) .eq
      (.app idx (.app threeXF (.var 0))) :=
    .cong (.appR idx (.appL .hole (.var 0))) (.beta atsub_f_le_idx)
  have s₅ : Red Γ₃ (.app idx (.app threeXF (.var 0))) .eq
      (.app idx (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0))))) :=
    .cong (.appR idx .hole) (.beta atsub_a_le_x)
  have s₆ : Red Γ₃
      (.app idx (.app (.var 1) (.app (.var 1) (.app (.var 1) (.var 0)))))
      .eq (.var 2) :=
    .beta atsub_fffa
  .head s₁ (.head s₂ (.head s₃ (.head s₄ (.head s₅ (.single s₆)))))

/-- `⊢A add(Nat)(3) ≡→* Nat`: two outer SRE-APP steps, then the body chain
under three SR-FUN steps, landing on `Nat`'s normal form. -/
private theorem redstar_add_nat_three :
    RedStar [] (.app (.app add nat) three) .eq nat :=
  have stepA : Red [] (.app (.app add nat) three) .eq (.app add₁ three) :=
    .cong (.appL .hole three) (.beta atsub_nat_le_nat)
  have stepB : Red [] (.app add₁ three) .eq addBody :=
    .beta atsub_three_le_nat
  .head stepA (.head stepB
    (RedStar.fn (RedStar.fn (RedStar.fn redstar_add_body))))

/-- §3.5.1: `Nat + 3 ≡ Nat` algorithmically — `add(Nat)(3)` evaluates to
`Nat` (abstract interpretation), with `Nat` in normal form on the right. -/
theorem nat_plus_three_eq_nat : ASub [] (.app (.app add nat) three) .eq nat :=
  ASub.of_join .nil redstar_add_nat_three .refl

end Pss.Examples
