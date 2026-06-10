import Pss.Star

/-!
# The §7 rewrite system (Hutchins, *Pure Subtype Systems*, POPL 2010)

§7 "An open problem" (p. 297) devises a rewrite system "which demonstrates
confluence behavior that is very similar to subtype reduction in System λ⊲,
but is formulated as a conventional ARS":

```
Terminals: A    Non-terminals: C, D
Let = be the symmetric and transitive closure of ⟶.
A        ⟶  C(A)
D(x, y)  ⟶  x     if x = y
D(x, y)  ⟶  y     if x = y
```

> "The above system is a conventional, first-order conditional rewrite
> system, without variables, contexts, or other complications."

so `⟶` is additionally closed under all argument positions (`congC`,
`congD₁`, `congD₂`). The projection rules are conditioned on `=`, which is
itself a closure of `⟶`, so `Step` (`⟶`) and `Conv` (`=`) are mutually
inductive — exactly like SRE-APP and `≤*` in Figure 2. The closures are
hand-rolled inside the mutual block: `Pss.Star` / `Pss.Sym` cannot be
applied to a relation that is still being defined.

`Conv` has **no** reflexivity constructor, staying literal to "the symmetric
and transitive closure of ⟶". Reflexivity is derivable anyway
(`Conv.refl`): every leaf of a term is the terminal `A` and `A ⟶ C(A)`, so
every term takes a step (`exists_step`), and `t = t` follows by symmetry and
transitivity through that reduct.
-/

namespace Pss
namespace SimpleARS

/-- Terms over the §7 signature: terminal `A`, non-terminals `C(·)` and
`D(·,·)`. -/
inductive Tm : Type where
  | A : Tm
  | C : Tm → Tm
  | D : Tm → Tm → Tm
deriving Repr, DecidableEq

mutual

/-- `t ⟶ t'` (§7, p. 297): the conditional rewrite rules, closed under all
argument positions. -/
inductive Step : Tm → Tm → Prop where
  /-- `A ⟶ C(A)`. -/
  | expand : Step .A (.C .A)
  /-- `D(x, y) ⟶ x if x = y`. -/
  | projL {x y : Tm} : Conv x y → Step (.D x y) x
  /-- `D(x, y) ⟶ y if x = y`. -/
  | projR {x y : Tm} : Conv x y → Step (.D x y) y
  /-- Closure under the argument of `C`. -/
  | congC {t t' : Tm} : Step t t' → Step (.C t) (.C t')
  /-- Closure under the first argument of `D`. -/
  | congD₁ {x x' y : Tm} : Step x x' → Step (.D x y) (.D x' y)
  /-- Closure under the second argument of `D`. -/
  | congD₂ {x y y' : Tm} : Step y y' → Step (.D x y) (.D x y')

/-- `t = t'` (§7): the symmetric and transitive closure of `⟶`. -/
inductive Conv : Tm → Tm → Prop where
  | step {t t' : Tm} : Step t t' → Conv t t'
  | symm {t t' : Tm} : Conv t t' → Conv t' t
  | trans {t₁ t₂ t₃ : Tm} : Conv t₁ t₂ → Conv t₂ t₃ → Conv t₁ t₃

end

/-- `t ⟶⟶ t'`: reduction sequences (`Pss.Star` applies once the mutual block
is closed). -/
abbrev Steps : Tm → Tm → Prop := Star Step

/-- `t ⟶⟶ s ⟵⟵ u`: joinability, the "transitivity-free form" of `=` that
§7 wants the conditions rewritten into. -/
def Joinable (t u : Tm) : Prop := ∃ s, Steps t s ∧ Steps u s

/-! ## Joint induction

Lean's `induction` tactic rejects the mutual block ("eliminator has multiple
motives"), so we provide the joint induction principle by hand from the
auto-generated recursors, following `Pss.Induction`. -/

section Induction

variable {motS motC : Tm → Tm → Prop}

variable
  (expand : motS .A (.C .A))
  (projL : ∀ {x y : Tm}, Conv x y → motC x y → motS (.D x y) x)
  (projR : ∀ {x y : Tm}, Conv x y → motC x y → motS (.D x y) y)
  (congC : ∀ {t t' : Tm}, Step t t' → motS t t' → motS (.C t) (.C t'))
  (congD₁ : ∀ {x x' y : Tm}, Step x x' → motS x x' → motS (.D x y) (.D x' y))
  (congD₂ : ∀ {x y y' : Tm}, Step y y' → motS y y' → motS (.D x y) (.D x y'))
  (cstep : ∀ {t t' : Tm}, Step t t' → motS t t' → motC t t')
  (csymm : ∀ {t t' : Tm}, Conv t t' → motC t t' → motC t' t)
  (ctrans : ∀ {t₁ t₂ t₃ : Tm}, Conv t₁ t₂ → Conv t₂ t₃ →
    motC t₁ t₂ → motC t₂ t₃ → motC t₁ t₃)

include expand projL projR congC congD₁ congD₂ cstep csymm ctrans

/-- Joint induction over the §7 mutual block. -/
theorem sars_induction :
    (∀ t t', Step t t' → motS t t') ∧ (∀ t t', Conv t t' → motC t t') := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_⟩
  · exact Step.rec (motive_1 := fun a b _ => motS a b)
      (motive_2 := fun a b _ => motC a b)
      expand
      (fun a ih => projL a ih)
      (fun a ih => projR a ih)
      (fun a ih => congC a ih)
      (fun a ih => congD₁ a ih)
      (fun a ih => congD₂ a ih)
      (fun a ih => cstep a ih)
      (fun a ih => csymm a ih)
      (fun a a' ih ih' => ctrans a a' ih ih')
      h
  · exact Conv.rec (motive_1 := fun a b _ => motS a b)
      (motive_2 := fun a b _ => motC a b)
      expand
      (fun a ih => projL a ih)
      (fun a ih => projR a ih)
      (fun a ih => congC a ih)
      (fun a ih => congD₁ a ih)
      (fun a ih => congD₂ a ih)
      (fun a ih => cstep a ih)
      (fun a ih => csymm a ih)
      (fun a a' ih ih' => ctrans a a' ih ih')
      h

/-- Induction over `⟶` derivations (projection of `sars_induction`). -/
theorem Step.induct {t t' : Tm} (h : Step t t') : motS t t' :=
  (sars_induction expand projL projR congC congD₁ congD₂
    cstep csymm ctrans).1 t t' h

/-- Induction over `=` derivations (projection of `sars_induction`). -/
theorem Conv.induct {t t' : Tm} (h : Conv t t') : motC t t' :=
  (sars_induction expand projL projR congC congD₁ congD₂
    cstep csymm ctrans).2 t t' h

end Induction

/-! ## Basic facts -/

/-- Every term can take a step: every leaf is the terminal `A`, and
`A ⟶ C(A)`. -/
theorem exists_step : ∀ t : Tm, ∃ t', Step t t'
  | .A => ⟨.C .A, .expand⟩
  | .C t => let ⟨t', h⟩ := exists_step t; ⟨.C t', .congC h⟩
  | .D x y => let ⟨x', h⟩ := exists_step x; ⟨.D x' y, .congD₁ h⟩

/-- `=` is reflexive even though the §7 definition is only the
symmetric-and-transitive closure: `t = t' = t` through any reduct `t'` of
`t`, and `exists_step` always supplies one. -/
theorem Conv.refl (t : Tm) : Conv t t :=
  let ⟨_, h⟩ := exists_step t
  (Conv.step h).trans (Conv.symm (Conv.step h))

/-- `=` is a congruence with respect to any `⟶`-preserving term former. -/
theorem Conv.map (F : Tm → Tm) (hF : ∀ {a b : Tm}, Step a b → Step (F a) (F b))
    {t u : Tm} (h : Conv t u) : Conv (F t) (F u) :=
  h.induct
    (motS := fun a b => Conv (F a) (F b))
    (motC := fun a b => Conv (F a) (F b))
    (expand := .step (hF .expand))
    (projL := fun h _ => .step (hF (.projL h)))
    (projR := fun h _ => .step (hF (.projR h)))
    (congC := fun h _ => .step (hF (.congC h)))
    (congD₁ := fun h _ => .step (hF (.congD₁ h)))
    (congD₂ := fun h _ => .step (hF (.congD₂ h)))
    (cstep := fun _ ih => ih)
    (csymm := fun _ ih => ih.symm)
    (ctrans := fun _ _ ih₁ ih₂ => ih₁.trans ih₂)

/-- `=` is closed under the argument of `C`. -/
theorem Conv.congC {t t' : Tm} (h : Conv t t') : Conv (.C t) (.C t') :=
  Conv.map Tm.C (fun hs => .congC hs) h

/-- `=` is closed under the first argument of `D`. -/
theorem Conv.congD₁ (y : Tm) {x x' : Tm} (h : Conv x x') :
    Conv (.D x y) (.D x' y) :=
  Conv.map (fun a => Tm.D a y) (fun hs => .congD₁ hs) h

/-- `=` is closed under the second argument of `D`. -/
theorem Conv.congD₂ (x : Tm) {y y' : Tm} (h : Conv y y') :
    Conv (.D x y) (.D x y') :=
  Conv.map (Tm.D x) (fun hs => .congD₂ hs) h

/-! ## The local diagram (§7, p. 297)

> "Much like subtype reduction, it gives rise to the following diagram of
> local confluence: [D(a,b) ⟶ a along the bottom, D(a,b) ⟶ b up the side,
> completed by b ⟶⟶ · ⟵⟵ a]. The condition on D(a,b) ⟶ a tells us that
> a = b. Given an appropriate induction hypothesis, we could transform a = b
> into a transitivity-free form, giving us a ⟶⟶ · ⟵⟵ b, which are the
> completing edges of the diagram."
-/

/-- The spanning edges of the §7 diagram: under the condition `a = b`, the
peak `a ⟵ D(a,b) ⟶ b` exists, and its reducts are related precisely by the
condition as given. -/
theorem d_local_diagram {a b : Tm} (h : Conv a b) :
    Step (.D a b) a ∧ Step (.D a b) b ∧ Conv a b :=
  ⟨.projL h, .projR h, h⟩

/-- **Local commutation up to `=`**: any two one-step reducts of a common
term are convertible. This is the §7 local diagram with the `=` condition
left "as given" — replacing the `Conv t₁ t₂` conclusion by joinability is
exactly the open transitivity-elimination content of
`Pss.Statements.simpleARS_confluent`. -/
theorem Step.local_conv {t t₁ : Tm} (h₁ : Step t t₁) :
    ∀ {t₂ : Tm}, Step t t₂ → Conv t₁ t₂ := by
  refine h₁.induct
    (motS := fun a b => ∀ {c : Tm}, Step a c → Conv b c)
    (motC := fun _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_
    (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ _ _ => trivial)
  · intro c h₂
    cases h₂ with
    | expand => exact Conv.refl _
  · intro x y hxy _ c h₂
    cases h₂ with
    | projL h => exact Conv.refl x
    | projR h => exact hxy
    | congD₁ hx =>
      exact (Conv.step hx).trans (Conv.symm (Conv.step
        (Step.projL ((Conv.symm (Conv.step hx)).trans hxy))))
    | congD₂ hy =>
      exact Conv.symm (Conv.step (Step.projL (hxy.trans (Conv.step hy))))
  · intro x y hxy _ c h₂
    cases h₂ with
    | projL h => exact Conv.symm hxy
    | projR h => exact Conv.refl y
    | congD₁ hx =>
      exact Conv.symm (Conv.step
        (Step.projR ((Conv.symm (Conv.step hx)).trans hxy)))
    | congD₂ hy =>
      exact (Conv.step hy).trans (Conv.symm (Conv.step
        (Step.projR (hxy.trans (Conv.step hy)))))
  · intro t t' hst ih c h₂
    cases h₂ with
    | congC h => exact Conv.congC (ih h)
  · intro x x' y hx ih c h₂
    cases h₂ with
    | projL hxy =>
      exact (Conv.step (Step.projL ((Conv.symm (Conv.step hx)).trans hxy))).trans
        (Conv.symm (Conv.step hx))
    | projR hxy =>
      exact Conv.step (Step.projR ((Conv.symm (Conv.step hx)).trans hxy))
    | congD₁ hx₂ => exact Conv.congD₁ y (ih hx₂)
    | congD₂ hy =>
      exact (Conv.symm (Conv.step (Step.congD₁ hx))).trans
        (Conv.step (Step.congD₂ hy))
  · intro x y y' hy ih c h₂
    cases h₂ with
    | projL hxy =>
      exact Conv.step (Step.projL (hxy.trans (Conv.step hy)))
    | projR hxy =>
      exact (Conv.step (Step.projR (hxy.trans (Conv.step hy)))).trans
        (Conv.symm (Conv.step hy))
    | congD₁ hx =>
      exact (Conv.symm (Conv.step (Step.congD₂ hy))).trans
        (Conv.step (Step.congD₁ hx))
    | congD₂ hy₂ => exact Conv.congD₂ x (ih hy₂)

/-! ## `=` versus joinability -/

/-- Reduction sequences are convertibility proofs. -/
theorem conv_of_steps {t u : Tm} (h : Steps t u) : Conv t u := by
  induction h with
  | refl => exact Conv.refl _
  | head hstep _ ih => exact (Conv.step hstep).trans ih

/-- Joinability is the "transitivity-free form" of `=`: `t ⟶⟶ s ⟵⟵ u`
implies `t = u`. The converse is the open content of §7. -/
theorem conv_of_joinable {t u : Tm} (h : Joinable t u) : Conv t u :=
  let ⟨_, h₁, h₂⟩ := h
  (conv_of_steps h₁).trans (Conv.symm (conv_of_steps h₂))

end SimpleARS

namespace Statements

/-- **The §7 conjecture (p. 297): the rewrite system is confluent.**

> "We conjecture that if a proof of confluence can be derived for the above
> rewrite system, then that proof can be adapted to show that ⟶≤ and ⟶≡
> commute in System λ⊲. Moreover, if a counter-example to confluence can be
> derived from the above rewrite system, then that counter-example can also
> be adapted to disprove commutativity, and consequently type safety, for
> System λ⊲."

Open problem in the paper; stated here as a `Prop` (never an axiom). -/
def simpleARS_confluent : Prop :=
  ∀ t t₁ t₂ : SimpleARS.Tm, SimpleARS.Steps t t₁ → SimpleARS.Steps t t₂ →
    ∃ t₃, SimpleARS.Steps t₁ t₃ ∧ SimpleARS.Steps t₂ t₃

end Statements

namespace SimpleARS

/-- Transitivity elimination from confluence (the §7 analogue of Lemma 6.3):
under `Pss.Statements.simpleARS_confluent`, every `=` condition can be
"transformed into a transitivity-free form, giving us a ⟶⟶ · ⟵⟵ b" — i.e.
the completing edges of the §7 local diagram. -/
theorem conv_joinable_of_confluent (hconf : Statements.simpleARS_confluent)
    {t u : Tm} (h : Conv t u) : Joinable t u :=
  h.induct
    (motS := fun a b => Joinable a b)
    (motC := fun a b => Joinable a b)
    (expand := ⟨.C .A, Star.single .expand, .refl⟩)
    (projL := fun h _ => ⟨_, Star.single (.projL h), .refl⟩)
    (projR := fun h _ => ⟨_, Star.single (.projR h), .refl⟩)
    (congC := fun h _ => ⟨_, Star.single (.congC h), .refl⟩)
    (congD₁ := fun h _ => ⟨_, Star.single (.congD₁ h), .refl⟩)
    (congD₂ := fun h _ => ⟨_, Star.single (.congD₂ h), .refl⟩)
    (cstep := fun _ ih => ih)
    (csymm := fun _ ih => let ⟨s, h₁, h₂⟩ := ih; ⟨s, h₂, h₁⟩)
    (ctrans := fun _ _ ih₁ ih₂ =>
      let ⟨_, ht₁, hm₁⟩ := ih₁
      let ⟨_, hm₂, hu₂⟩ := ih₂
      let ⟨s₃, hs₁, hs₂⟩ := hconf _ _ _ hm₁ hm₂
      ⟨s₃, ht₁.trans hs₁, hu₂.trans hs₂⟩)

/-- Under the §7 conjecture, `=` coincides with joinability. -/
theorem conv_iff_joinable_of_confluent (hconf : Statements.simpleARS_confluent)
    {t u : Tm} : Conv t u ↔ Joinable t u :=
  ⟨conv_joinable_of_confluent hconf, conv_of_joinable⟩

end SimpleARS

end Pss
