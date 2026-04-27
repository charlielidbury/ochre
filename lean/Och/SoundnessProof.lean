import Och.NbE
import Och.SubCheckVal
import Och.Subtyping
import Och.TyCheck

/-!
# `subCheckVal_sound`: the arm-by-arm proof

`Soundness.lean` states the target theorems; this file builds
the proof of the algorithmic-→-declarative direction. The
strategy is fuel induction on `subCheckVal` (now non-partial),
with one case per match arm.

The bridge between the `Val` domain (algorithm) and the `Expr`
domain (`Subtype'`) is `quote`. Rather than thread `quote`
through every IH, we work with a *Val-level relation* `SubV`
that mirrors `subCheckVal` arm-for-arm; the algorithm-→-`SubV`
direction is then a direct fuel induction with no
representation change. Relating `SubV` to the Expr-level
`Subtype'` (the quote bridge) is a separate lemma, factored
out so it can be attacked independently.

  subCheckVal ──(this file)──▶ SubV ──(quote bridge)──▶ Subtype'

This file currently proves the *guard arms* (refl, top, hyp)
of `subCheckVal_subV` and records exactly which supporting
lemmas the remaining arms need.
-/

namespace NbE

/-!
## Fuel-erased helpers

`SubV` is stated without a fuel parameter; the fuelled
algorithm's `cl.open fuel` results are lifted to a large
fixed budget. The eventual quote-bridge lemma needs
fuel-monotonicity for `eval` (recorded below as a sorried
lemma) so this is sound.
-/

def fuelω : Nat := 100000

def Closure.openω (cl : Closure) (v : Val) : Option Val :=
  (cl.open fuelω v).toOption

def vappω (f a : Val) : Option Val :=
  (vapp fuelω 4 f a).toOption

/-!
## The Val-level relation
-/

mutual
  /-- Val-level declarative subtyping. One constructor per
  `subCheckVal` arm that can return `.ok true`. -/
  inductive SubV : List (Val × Val) → TyCtx → Val → Val → Prop where
    | hyp {S Γ a b} : (a, b) ∈ S → SubV S Γ a b
    | refl {S Γ a} : SubV S Γ a a
    | top {S Γ a} : SubV S Γ a .type
    | lam {S Γ domA domB clA clB bA bB} :
        clA.openω (.neutral (.var Γ.size)) = some bA →
        clB.openω (.neutral (.var Γ.size)) = some bB →
        SubV S Γ domB domA →
        -- Push `domB` (narrower / target), matching the algorithm
        -- post-och-refactor flip and `Subtype'.lam`. The previous
        -- `domA` push was a perf workaround; flipped 2026-04-27.
        SubV S (Γ.push domB) bA bB →
        SubV S Γ (.lam domA clA) (.lam domB clB)
    | iota_struct {S Γ annA annB clA clB bA bB} :
        clA.openω (.neutral (.var Γ.size)) = some bA →
        clB.openω (.neutral (.var Γ.size)) = some bB →
        SubV ((.iota annA clA, .iota annB clB) :: S) Γ annA annB →
        SubV ((.iota annA clA, .iota annB clB) :: S) (Γ.push annB) bA bB →
        SubV S Γ (.iota annA clA) (.iota annB clB)
    | fix_struct {S Γ annA annB clA clB bA bB} :
        clA.openω (.neutral (.var Γ.size)) = some bA →
        clB.openω (.neutral (.var Γ.size)) = some bB →
        SubV ((.«fix» annA clA, .«fix» annB clB) :: S) Γ annA annB →
        SubV ((.«fix» annA clA, .«fix» annB clB) :: S) (Γ.push annB) bA bB →
        SubV S Γ (.«fix» annA clA) (.«fix» annB clB)
    | stuckRec_struct {S Γ fA aA fB aB} :
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ fA fB →
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ fB fA →
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ aA aB →
        SubV ((.neutral (.stuckRec fA aA),
               .neutral (.stuckRec fB aB)) :: S) Γ aB aA →
        SubV S Γ (.neutral (.stuckRec fA aA))
                  (.neutral (.stuckRec fB aB))
    | iota_intro {S Γ a ann clB bB} :
        clB.openω a = some bB →
        SubV ((a, .iota ann clB) :: S) Γ a ann →
        SubV ((a, .iota ann clB) :: S) Γ a bB →
        SubV S Γ a (.iota ann clB)
    | unfold_fix_R {S Γ a ann clB bB} :
        clB.openω (.«fix» ann clB) = some bB →
        SubV ((a, .«fix» ann clB) :: S) Γ a bB →
        SubV S Γ a (.«fix» ann clB)
    | unfold_fix_L {S Γ ann clA bA c} :
        clA.openω (.«fix» ann clA) = some bA →
        -- Productivity (A7): without this, body = `.bvar 0`
        -- gives `bA = a` and the recursive premise closes by
        -- `.hyp`, deriving `(fix self. self) ⊑ c` for every c
        -- — unsound (`⊤ ⊄ c` for c ≠ ⊤). The R-side
        -- `unfold_fix_R` needs no guard (`a ⊑ ⊤` is true).
        bA ≠ .«fix» ann clA →
        SubV ((.«fix» ann clA, c) :: S) Γ bA c →
        SubV S Γ (.«fix» ann clA) c
    | unfold_iota_L {S Γ ann clA bA c} :
        clA.openω (.iota ann clA) = some bA →
        bA ≠ .iota ann clA →
        SubV ((.iota ann clA, c) :: S) Γ bA c →
        SubV S Γ (.iota ann clA) c
    | neutral_struct {S Γ nA nB} :
        SubN S Γ nA nB →
        SubV S Γ (.neutral nA) (.neutral nB)
    | neutral_ascent {S Γ nA τ b} :
        SynthN Γ nA τ →
        SubV S Γ τ b →
        SubV S Γ (.neutral nA) b
    | revapp_R {S Γ a f arg b'} :
        -- The algorithm only reaches re-application when the
        -- RHS is a stuck recursive head; `b'` is the result
        -- of forcing one more unfold via `vappω`. WITHOUT this
        -- premise (just `b' ≠ b → … → SubV S Γ a b`) the
        -- constructor lets `b'` be arbitrary — instantiating
        -- `b' := .type` and discharging the recursive premise
        -- by `.top` made `SubV S Γ a b` hold for *every* a, b
        -- (bughunt-lite, 5-0). The `vappω` premise ties `b'`
        -- to `f arg`'s one-step unfold, matching exactly what
        -- the proof at `subCheckValMatch_subV`'s stuckRec arms
        -- already binds as `hvapp` and discards.
        vappω f arg = some b' →
        b' ≠ .neutral (.stuckRec f arg) →
        SubV ((a, .neutral (.stuckRec f arg)) :: S) Γ a b' →
        SubV S Γ a (.neutral (.stuckRec f arg))
    | revapp_L {S Γ f arg a' c} :
        vappω f arg = some a' →
        a' ≠ .neutral (.stuckRec f arg) →
        SubV ((.neutral (.stuckRec f arg), c) :: S) Γ a' c →
        SubV S Γ (.neutral (.stuckRec f arg)) c
    /-- [S-BotL]: Bot ⊑ anything. Val-level mirror of
        `Subtype'.bot_L`. See `docs/ideas/bottom.md`. -/
    | bot_L {S Γ b} : SubV S Γ .bot b

  /-- Val-level neutral congruence (mirrors `subCheckNeutral`). -/
  inductive SubN : List (Val × Val) → TyCtx → Neutral → Neutral → Prop where
    | var {S Γ k} : SubN S Γ (.var k) (.var k)
    | app {S Γ n1 n2 v1 v2} :
        SubN S Γ n1 n2 → SubV S Γ v1 v2 → SubV S Γ v2 v1 →
        SubN S Γ (.app n1 v1) (.app n2 v2)
    | stuckRec {S Γ fA aA fB aB} :
        SubV S Γ fA fB → SubV S Γ fB fA →
        SubV S Γ aA aB → SubV S Γ aB aA →
        SubN S Γ (.stuckRec fA aA) (.stuckRec fB aB)

  /-- Type synthesis for neutrals (mirrors `synthNeutral`). -/
  inductive SynthN : TyCtx → Neutral → Val → Prop where
    | var {Γ k τ} : Γ[k]? = some τ → SynthN Γ (.var k) τ
    | app {Γ n v dom cl τ} :
        SynthN Γ n (.lam dom cl) → cl.openω v = some τ →
        SynthN Γ (.app n v) τ
    | stuckRecFix {Γ ann cl arg dom cl' τ} :
        ann = .lam dom cl' → cl'.openω arg = some τ →
        SynthN Γ (.stuckRec (.«fix» ann cl) arg) τ
    | stuckRecIota {Γ ann cl arg dom cl' τ} :
        ann = .lam dom cl' → cl'.openω arg = some τ →
        SynthN Γ (.stuckRec (.iota ann cl) arg) τ
    /-- When the recursive head's annotation is not a Π, the
    algorithm returns the bare annotation. -/
    | stuckRecFixAnn {Γ ann cl arg} :
        (∀ d c, ann ≠ .lam d c) →
        SynthN Γ (.stuckRec (.«fix» ann cl) arg) ann
    | stuckRecIotaAnn {Γ ann cl arg} :
        (∀ d c, ann ≠ .lam d c) →
        SynthN Γ (.stuckRec (.iota ann cl) arg) ann
end

/-!
## Algorithm → `SubV`: the guard arms

The first three guards in `subCheckVal` (`a == b`, `b == .type`,
`(a,b) ∈ seen`) map directly to `.refl`/`.top`/`.hyp`. These are
proved here; the match arms (lam-lam, iota, fix, neutral) are
sorried with the supporting-lemma they need recorded below.
-/

/-- Membership decision: the `seen.any` guard. The algorithm
checks `a == a' && b == b'` (line 71); reflect into `∈` via
the `LawfulBEq Val` instance. -/
theorem seen_any_mem {S : List (Val × Val)} {a b : Val}
    (h : (S.any fun (a', b') => a == a' && b == b') = true) :
    (a, b) ∈ S := sorry
theorem Closure.openω_of_open {cl : Closure} {v r : Val} {n : Nat}
    (hn : n ≤ fuelω) (h : cl.open n v = .ok r) :
    cl.openω v = some r := sorry
theorem vappω_of_vapp {f arg r : Val} {n : Nat}
    (hn : n ≤ fuelω) (h : vapp n 4 f arg = .ok r) :
    vappω f arg = some r := sorry
theorem openω_of_toOption {cl : Closure} {v r : Val} {n : Nat}
    (hn : n ≤ fuelω) (h : (cl.open n v).toOption = some r) :
    cl.openω v = some r := sorry
theorem Closure.openω_of_openFresh {cl : Closure} {r : Val}
    {n depth : Nat} (hn : n ≤ fuelω)
    (h : cl.openFresh n depth = .ok r) :
    cl.openω (.neutral (.var depth)) = some r := sorry
theorem Val.ne_of_beq_false {a b : Val} (h : (a == b) = false) :
    a ≠ b := sorry
mutual

theorem subCheckVal_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckVal fuel Γ S a b = .ok true) :
    SubV S Γ a b := sorry
theorem subCheckValMatch_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {a b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckValMatch fuel Γ S a b = .ok true) :
    SubV S Γ a b := sorry
theorem subCheckNeutral_subN
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {nA nB : Neutral}
    (hfuel : fuel ≤ fuelω)
    (h : subCheckNeutral fuel Γ S nA nB = .ok true) :
    SubN S Γ nA nB := sorry
theorem neutralAscent_subV
    {fuel : Nat} {Γ : TyCtx} {S : List (Val × Val)} {nA : Neutral} {b : Val}
    (hfuel : fuel ≤ fuelω)
    (h : neutralAscent fuel Γ S nA b = .ok true) :
    SubV S Γ (.neutral nA) b := sorry
theorem synthNeutral_synthN
    {fuel : Nat} {Γ : TyCtx} {nA : Neutral} {τ : Val}
    (hfuel : fuel ≤ fuelω)
    (h : synthNeutral fuel Γ nA = .ok (some τ)) :
    SynthN Γ nA τ := sorry
end

/-!
## The quote bridge

`SubV` is over `Val`s; `Subtype'` is over `Expr`s. The bridge
quotes each piece. Three lemmas factor the work:

  - `quote_lam`/`quote_iota`/`quote_fix` (shape lemmas):
    `quote (.lam d c) = .ok e → ∃ de be, e = .lam de be ∧ …`
  - `quote_open` (NbE correctness): the quoted body of a
    closure opened with `v` is β-related to the substituted
    quote. This is the substantive lemma; everything else
    is bookkeeping.
  - Context/seen quoting respects extension (for the IH at
    `Γ.push`/`(p :: S)`).
-/

/-!
### The unf-mismatch blocker

`Closure.openω cl v = eval fuelω 4 (v :: cl.env) cl.body`
(unf = **4**), but `quoteClosure (n+1) d cl` evaluates the
body at unf = **1** before quoting. So even when `v` is the
fresh neutral `.var d`, the two evaluations can differ
whenever `cl.body` contains a *closed* recursive
application (e.g. `Array_ done_` captured in the env): at
unf=4 it unfolds three times, at unf=1 once. Hence
`quote (d+1) (cl.openω fresh) ≠ quoteClosure d cl` in
general — the directive's hoped-for `rfl` does not hold.

What does hold is that the two `eval` results are related
by repeated fix/iota unfolds, which `Subtype'.unfold_fix_*`
/`unfold_iota_L` capture. The precise sub-lemma:
-/

/-!
### Logical relation for NbE correctness

The standard NbE soundness proof factors through a
*realisability* relation between semantic values and source
expressions. We use a step-indexed version (the `.lam`
clause quantifies over smaller indices, so the definition
terminates by recursion on the step count).
-/

/-- `Subtype'`-equivalence: both directions, in every
seen/context. This is the equational theory the bridge
targets. -/
def Equiv (e₁ e₂ : Expr) : Prop :=
  ∀ {S : Seen} {Γe : Ctx}, Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁

namespace Equiv
  theorem refl (e : Expr) : Equiv e e := sorry
  theorem symm {e₁ e₂} (h : Equiv e₁ e₂) : Equiv e₂ e₁ := sorry
  theorem trans {e₁ e₂ e₃} (h₁ : Equiv e₁ e₂) (h₂ : Equiv e₂ e₃) :
      Equiv e₁ e₃ := sorry
  theorem lam {dom₁ dom₂ body₁ body₂ : Expr}
      (hd : Equiv dom₁ dom₂) (hb : Equiv body₁ body₂) :
      Equiv (.lam dom₁ body₁) (.lam dom₂ body₂) := sorry
  theorem app {f₁ f₂ a₁ a₂ : Expr}
      (hf : Equiv f₁ f₂) (ha : Equiv a₁ a₂) :
      Equiv (.app f₁ a₁) (.app f₂ a₂) := sorry
  theorem shift_of_closed {e₁ e₂ : Expr}
      (h₁ : e₁.closedAt 0 = true) (h₂ : e₂.closedAt 0 = true)
      (h : Equiv e₁ e₂) :
      Equiv (e₁.shift 1 0) (e₂.shift 1 0) := sorry
  theorem subst_resp_closed :
      ∀ (e : Expr) {a b : Expr},
      a.closedAt 0 = true → b.closedAt 0 = true →
      Equiv a b → ∀ (i : Nat),
      Equiv (e.subst i a) (e.subst i b) := sorry
end Equiv

/-! ### Depth-parametrised Equiv (`Equiv_c`)

`Equiv_c d e₁ e₂` says `e₁ ⊑ e₂` and `e₂ ⊑ e₁` at every
context `Γ` of length **at least** `d`. This is strictly
weaker than `Equiv` (which requires `|Γ| ≥ 0` = all `Γ`,
including `[]`).

**Why it exists:** `Equiv.shift` at `Γ = []` is unprovable
without closedness of both endpoints (the structural blocker
documented in DECISION-LOG 2026-04-21). But at `Γ ≠ []`, the
shift follows from `Subtype'.ctx_extend`, which is already
proven. `Equiv_c d` excludes `Γ = []` for `d ≥ 1`, restoring
provability of shift without any closedness side condition.

`Equiv_c 0` coincides with `Equiv` (both quantify over all
`Γ`), so at the top-level soundness chain (`Γe = []`, closed
terms) no information is lost. For internal uses (R's closure
clauses at depth `d ≥ 1`), `Equiv_c d` is enough because
all downstream consumers use it at a `Γe` of length `d`. -/
@[reducible]
def Equiv_c (d : Nat) (e₁ e₂ : Expr) : Prop :=
  ∀ {S : Seen} {Γe : Ctx}, d ≤ Γe.length →
    Subtype' S Γe e₁ e₂ ∧ Subtype' S Γe e₂ e₁

namespace Equiv_c
  theorem refl (d : Nat) (e : Expr) : Equiv_c d e e := sorry
  theorem symm {d e₁ e₂} (h : Equiv_c d e₁ e₂) : Equiv_c d e₂ e₁ := sorry
  theorem trans {d e₁ e₂ e₃}
      (h₁ : Equiv_c d e₁ e₂) (h₂ : Equiv_c d e₂ e₃) :
      Equiv_c d e₁ e₃ := sorry
  theorem of_Equiv {d e₁ e₂} (h : Equiv e₁ e₂) : Equiv_c d e₁ e₂ := sorry
  theorem mono {d d' e₁ e₂} (hle : d ≤ d')
      (h : Equiv_c d e₁ e₂) : Equiv_c d' e₁ e₂ := sorry
  theorem lam_cong {d domA domB bodyA bodyB}
      (hd : Equiv_c d domA domB) (hb : Equiv_c (d+1) bodyA bodyB) :
      Equiv_c d (.lam domA bodyA) (.lam domB bodyB) := sorry
  theorem iota_cong {d ann₁ ann₂ body₁ body₂}
      (ha : Equiv_c d ann₁ ann₂)
      (hb : Equiv_c (d+1) body₁ body₂) :
      Equiv_c d (.iota ann₁ body₁) (.iota ann₂ body₂) := sorry
  theorem fix_cong {d ann₁ ann₂ body₁ body₂}
      (ha : Equiv_c d ann₁ ann₂)
      (hb : Equiv_c (d+1) body₁ body₂) :
      Equiv_c d (.fix ann₁ body₁) (.fix ann₂ body₂) := sorry
  theorem app_cong {d f₁ f₂ a₁ a₂}
      (hf : Equiv_c d f₁ f₂) (ha : Equiv_c d a₁ a₂) :
      Equiv_c d (.app f₁ a₁) (.app f₂ a₂) := sorry
  theorem to_Equiv_zero {e₁ e₂} (h : Equiv_c 0 e₁ e₂) : Equiv e₁ e₂ := sorry
  theorem shift {d e₁ e₂} (h : Equiv_c d e₁ e₂) :
      Equiv_c (d+1) (e₁.shift 1 0) (e₂.shift 1 0) := sorry
  theorem subst_resp (body : Expr) {d a b}
      (heq : Equiv_c d a b) (i : Nat) :
      Equiv_c d (body.subst i a) (body.subst i b) := sorry
end Equiv_c

/-! ## Step-indexed logical relation

`R n d v e` means "at step index `n` and depth `d`, the
value `v` realises the expression `e`".

The constructor-specific conjunct for `.lam`/`.iota`/`.fix`
**exposes the closure's environment AND the head annotation**
as realised at the *same* step index `n+1`: `∃ ρe' he,
R (n+1) d headV he ∧ RList (n+1) d cl.env ρe' ∧ …
∧ Equiv e (.lam he (body.substEnv (lift ρe')))`. This lets
`vapp_realises`'s `.lam`-head case build
`REnv (n+1) d (a :: cl.env) (ae :: ρe')` and call
`eval_realises`'s fuel-IH directly — no Kripke step-loss.

The former *base conjunct* (`∀ e', quote fuelω d v = .ok e'
→ Equiv e' e`) was dropped 2026-04-21: it's unprovable inside
`eval_realises`'s fuel-IH (`quoteClosure`'s inner eval is at
`fuelω-1`, outside the IH). Recovered post-hoc as the
external `R_quote_equiv` via mutual recursion with
`quoteClosure_realises` on **quote-fuel** — see DECISION-LOG
2026-04-19.

The previous Kripke design (`∀ n' ≤ n, … → R n' d r …`) lost
one step-index at every `.app`-head boundary, leaving
`vapp_realises` unprovable (see the docstring there for the
detailed analysis of why both `(fuel,unf)`-lex and Ahmed-style
indexing also fail by exactly 1).

Termination: `R`/`RList` are mutual on `(n, sizeOf v)` lex.
The same-index recursion `R (n+1) d w …` for `w ∈ cl.env` and
for the head annotation is well-founded because
`sizeOf w < sizeOf cl.env < sizeOf cl < sizeOf (.lam _ cl)`,
and `sizeOf headV < sizeOf (.lam headV cl)`. -/

-- Val.levelsBelow / Val.fullyQuotable: defined here (before R)
-- so R's closure clauses can reference envLevelsBelow /
-- envFullyQuotable as invariants. Moved up 2026-04-22 as
-- prep for quoteClosure_realises refactor.
mutual
  /-- `Val.levelsBelow d v` iff every neutral-var level in `v` is
  `< d`. -/
  def Val.levelsBelow (d : Nat) : Val → Prop
    | .type => True
    | .bot => True
    | .neutral n => Neutral.levelsBelow d n
    | .lam dom cl => Val.levelsBelow d dom ∧ Closure.levelsBelow d cl
    | .iota ann cl => Val.levelsBelow d ann ∧ Closure.levelsBelow d cl
    | .«fix» ann cl => Val.levelsBelow d ann ∧ Closure.levelsBelow d cl

  def Neutral.levelsBelow (d : Nat) : Neutral → Prop
    | .var k => k < d
    | .app n v => Neutral.levelsBelow d n ∧ Val.levelsBelow d v
    | .stuckRec f a => Val.levelsBelow d f ∧ Val.levelsBelow d a

  def Closure.levelsBelow (d : Nat) : Closure → Prop
    | ⟨_body, env⟩ => Closure.envLevelsBelow d env

  /-- Helper for Closure.levelsBelow (inlined list quantifier). -/
  def Closure.envLevelsBelow (d : Nat) : List Val → Prop
    | [] => True
    | v :: vs => Val.levelsBelow d v ∧ Closure.envLevelsBelow d vs
end

/-! ### `Val.fullyQuotable`: recursive quotability through closure envs.

`Val.fullyQuotable d v` says: `v` is quotable at depth `d` AND every
Val reachable via `v`'s transitive closure-environments is quotable
at depth `d`. This is the invariant needed by R_depth_lift's closure
cases: when RList_depth_lift recurses into each `cl.env` entry, it
needs a quote witness for that entry, and if the entry is itself a
closure, quote witnesses for ITS env, and so on. -/
mutual
  def Val.fullyQuotable (d : Nat) : Val → Prop
    | .type => True
    | .bot => True
    | .neutral n => Neutral.fullyQuotable d n
    | .lam dom cl => Val.fullyQuotable d dom ∧ Closure.fullyQuotable d cl
    | .iota ann cl => Val.fullyQuotable d ann ∧ Closure.fullyQuotable d cl
    | .«fix» ann cl => Val.fullyQuotable d ann ∧ Closure.fullyQuotable d cl

  def Neutral.fullyQuotable (d : Nat) : Neutral → Prop
    | .var k => k < d
    | .app n v => Neutral.fullyQuotable d n ∧ Val.fullyQuotable d v
    | .stuckRec f a => Val.fullyQuotable d f ∧ Val.fullyQuotable d a

  def Closure.fullyQuotable (d : Nat) : Closure → Prop
    | ⟨body, env⟩ =>
        body.closedAt (env.length + 1) = true ∧ Closure.envFullyQuotable d env

  /-- Each env entry is fully quotable AND has a concrete quote
  witness at `d`. The quote witness is what RList_depth_lift's
  recursive R_depth_lift call needs. -/
  def Closure.envFullyQuotable (d : Nat) : List Val → Prop
    | [] => True
    | v :: vs =>
      (Val.fullyQuotable d v ∧ (∃ qe, quote fuelω d v = .ok qe)) ∧
      Closure.envFullyQuotable d vs
end

mutual
/-- See the `Step-indexed logical relation` section above. -/
def R : Nat → Nat → Val → Expr → Prop
  | 0, _, _, _ => True
  | n+1, d, v, e =>
      match v with
        | .lam dV cl =>
            -- Env-exposes only — no base conjunct for
            -- `.lam`/`.iota`/`.fix` (DECISION-LOG 2026-04-19).
            -- Recovered post-hoc by `R_quote_equiv` + mutual
            -- `quoteClosure_realises` on quote-fuel.
            --
            -- 2026-04-22: envLevelsBelow + envFullyQuotable
            -- carried so quoteClosure_realises can invoke
            -- RList_depth_lift + eval_realises at d+1.
            ∃ ρe' dome,
              R (n+1) d dV dome ∧
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Closure.envLevelsBelow d cl.env ∧
              Closure.envFullyQuotable d cl.env ∧
              Equiv_c d e (.lam dome
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .iota aV cl =>
            ∃ ρe' anne,
              R (n+1) d aV anne ∧
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Closure.envLevelsBelow d cl.env ∧
              Closure.envFullyQuotable d cl.env ∧
              Equiv_c d e (.iota anne
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        | .«fix» aV cl =>
            ∃ ρe' anne,
              R (n+1) d aV anne ∧
              RList (n+1) d cl.env ρe' ∧
              cl.body.closedAt (ρe'.length + 1) = true ∧
              Closure.envLevelsBelow d cl.env ∧
              Closure.envFullyQuotable d cl.env ∧
              Equiv_c d e (.fix anne
                (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))))
        -- `.type`/`.bot`/`.neutral` keep the base conjunct: quoting
        -- them doesn't recurse into environments, so the
        -- correspondence is provable inside `eval_realises`'s
        -- fuel-IH directly. Uses Equiv_c d (depth-parametrised
        -- Equiv) so R_depth_lift can close via Equiv_c.shift.
        | .type => ∀ e', quote fuelω d v = .ok e' → Equiv_c d e' e
        | .bot => ∀ e', quote fuelω d v = .ok e' → Equiv_c d e' e
        | .neutral _ => ∀ e', quote fuelω d v = .ok e' → Equiv_c d e' e
termination_by _ _ v _ => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename Closure => cl; cases cl; simp; omega)

/-- Pointwise list realisation, mutual with `R` so the
`.lam`/`.iota`/`.fix` clauses can reference it at the *same*
step-index (well-founded by `sizeOf`). Equivalent to the
indexed `REnv` form (see `REnv_iff_RList`). -/
def RList : Nat → Nat → List Val → List Expr → Prop
  | _, _, [], [] => True
  | n, d, v :: ρ, e :: ρe => R n d v e ∧ RList n d ρ ρe
  | _, _, [], _ :: _ => False
  | _, _, _ :: _, [] => False
termination_by _ _ ρ _ => sizeOf ρ
decreasing_by all_goals (simp_wf; omega)
end

/-- An environment `ρ` realises an expression-environment
`ρe` at index `n`, depth `d`. Indexed form, equivalent to the
mutual `RList` (see `REnv_iff_RList`). All env-level lemmas
are stated on `REnv`; conversion happens at `R`'s clause
boundary. -/
def REnv (n d : Nat) (ρ : Env) (ρe : List Expr) : Prop :=
  ρ.length = ρe.length ∧
  ∀ k v, ρ[k]? = some v → ∃ e, ρe.get? k = some e ∧ R n d v e

theorem RList_length {n d ρ ρe} (h : RList n d ρ ρe) :
    ρ.length = ρe.length := sorry
theorem REnv_iff_RList {n d ρ ρe} : REnv n d ρ ρe ↔ RList n d ρ ρe := sorry
theorem RList_of_REnv {n d ρ ρe} (h : REnv n d ρ ρe) :
    RList n d ρ ρe := sorry
theorem REnv_of_RList {n d ρ ρe} (h : RList n d ρ ρe) :
    REnv n d ρ ρe := sorry
mutual
/-- Downward closure: realisation at a larger step index
implies realisation at every smaller one. The constructor
clauses' `RList (n+1)` lowers via mutual `RList_mono`, and
the head annotation's `R (n+1)` via `R_mono` at `sizeOf
headV < sizeOf (.lam headV cl)`. -/
theorem R_mono {n m d v e} (hle : m ≤ n) (h : R n d v e) :
    R m d v e := sorry
theorem RList_mono {n m d ρ ρe} (hle : m ≤ n)
    (h : RList n d ρ ρe) : RList m d ρ ρe := sorry
end

theorem REnv_mono {n m d ρ ρe} (hle : m ≤ n) (h : REnv n d ρ ρe) :
    REnv m d ρ ρe := sorry
theorem R_resp_Equiv {n d v e e'}
    (heq : Equiv e e') (h : R n d v e) : R n d v e' := sorry
theorem R_resp_Equiv_c {n d v e e'}
    (heq : Equiv_c d e e') (h : R n d v e) : R n d v e' := sorry
theorem REnv_take {n d ρ ρe} (j : Nat) (h : REnv n d ρ ρe) :
    REnv n d (ρ.take j) (ρe.take j) := sorry
theorem closedAt_bvarBound (e : Expr) : e.closedAt (bvarBound e) = true := sorry
theorem bvarBound_le_of_closedAt {e : Expr} {n : Nat}
    (h : e.closedAt n = true) : bvarBound e ≤ n := sorry
theorem Closure.mk'_body_closed (body : Expr) (ρ : Env)
    (hρ : bvarBound body ≤ ρ.length + 1) :
    body.closedAt ((Closure.mk' body ρ).env.length + 1) = true := sorry
private theorem substEnv_bvar_eq (γ : List Expr) (k : Nat) :
    Expr.substEnv γ (.bvar k) = (γ[k]?).getD (.bvar k) := sorry
theorem substEnv_agree {e : Expr} :
    ∀ {j : Nat}, e.closedAt j = true →
    ∀ {γ₁ γ₂ : List Expr}, (∀ k, k < j → γ₁[k]? = γ₂[k]?) →
    e.substEnv γ₁ = e.substEnv γ₂ := sorry
theorem substEnv_closedAt {e : Expr} {n : Nat} {ρe : List Expr}
    (hbound : e.closedAt ρe.length = true)
    (hρecl : ∀ (k : Nat) (e' : Expr), ρe[k]? = some e' →
             e'.closedAt n = true) :
    (e.substEnv ρe).closedAt n = true := sorry
theorem substEnv_closedAt_irrel {e : Expr} {j : Nat}
    (hcl : e.closedAt (j+1) = true)
    {x : Expr} {ρe ρe' : List Expr}
    (hpfx : ρe' = ρe.take j) :
    e.substEnv (x :: ρe') = e.substEnv (x :: ρe) := sorry
theorem substEnv_shift_comm : ∀ (body : Expr) (γ : List Expr) (c : Nat),
    body.closedAt γ.length = true →
    (Expr.substEnv γ body).shift 1 c
      = Expr.substEnv (γ.map (·.shift 1 c)) body := sorry
mutual
  /-- Shift every neutral-var level `≥ c` up by 1. -/
  def Val.shiftLvl (c : Nat) : Val → Val
    | .type => .type
    | .bot => .bot
    | .neutral n => .neutral (Neutral.shiftLvl c n)
    | .lam dom cl => .lam (Val.shiftLvl c dom) (Closure.shiftLvl c cl)
    | .iota ann cl => .iota (Val.shiftLvl c ann) (Closure.shiftLvl c cl)
    | .«fix» ann cl => .«fix» (Val.shiftLvl c ann) (Closure.shiftLvl c cl)

  def Neutral.shiftLvl (c : Nat) : Neutral → Neutral
    | .var k => .var (if k < c then k else k + 1)
    | .app n v => .app (Neutral.shiftLvl c n) (Val.shiftLvl c v)
    | .stuckRec f a => .stuckRec (Val.shiftLvl c f) (Val.shiftLvl c a)

  def Closure.shiftLvl (c : Nat) : Closure → Closure
    | ⟨body, env⟩ => ⟨body, Closure.envShiftLvl c env⟩

  /-- Helper for Closure.shiftLvl (inlined `List.map`) so Lean's
  termination checker sees the recursive call into Val.shiftLvl. -/
  def Closure.envShiftLvl (c : Nat) : List Val → List Val
    | [] => []
    | v :: vs => Val.shiftLvl c v :: Closure.envShiftLvl c vs
end

theorem Val.shiftLvl_neutral_isNeutral (c : Nat) (v : Val) :
    (Val.shiftLvl c v).isNeutral = v.isNeutral := sorry
theorem Closure.envShiftLvl_eq_map (c : Nat) (env : List Val) :
    Closure.envShiftLvl c env = env.map (Val.shiftLvl c) := sorry
theorem Closure.envLevelsBelow_getElem?
    {d : Nat} {env : List Val}
    (h : Closure.envLevelsBelow d env)
    {k : Nat} {v : Val} (hk : env[k]? = some v) :
    Val.levelsBelow d v := sorry
theorem Closure.envLevelsBelow_of_getElem?
    {d : Nat} {env : List Val}
    (h : ∀ (k : Nat) (v : Val),
      List.get? env k = some v → Val.levelsBelow d v) :
    Closure.envLevelsBelow d env := sorry
mutual
/-- Shift is a no-op when levels are already below the cutoff.
Joint mutual theorem on Val / Neutral / Closure, proved by
structural recursion on sizeOf. -/
theorem Val.shiftLvl_of_levelsBelow :
    ∀ (v : Val) (c : Nat),
    Val.levelsBelow c v → Val.shiftLvl c v = v := sorry
theorem Neutral.shiftLvl_of_levelsBelow :
    ∀ (n : Neutral) (c : Nat),
    Neutral.levelsBelow c n → Neutral.shiftLvl c n = n := sorry
theorem Closure.shiftLvl_of_levelsBelow :
    ∀ (cl : Closure) (c : Nat),
    Closure.levelsBelow c cl → Closure.shiftLvl c cl = cl := sorry
theorem Closure.envShiftLvl_of_envLevelsBelow :
    ∀ (env : List Val) (c : Nat),
    Closure.envLevelsBelow c env → Closure.envShiftLvl c env = env := sorry
end

/-!
### `eval` commutes with `Val.shiftLvl`

`eval fuel unf ρ e = .ok v` ⇒
`eval fuel unf (ρ.map (Val.shiftLvl c)) e = .ok (v.shiftLvl c)`.

Proved by combined induction on fuel over `eval` and `vapp`. The
vapp-iota/fix branches case-split on `a`-shape (to evaluate
`Val.shiftLvl c a`.isNeutral) and on the `isNeutral || unf==0`
gate. -/

theorem eval_vapp_shiftLvl :
    ∀ n,
    (∀ {unf c ρ e v}, eval n unf ρ e = .ok v →
      eval n unf (ρ.map (Val.shiftLvl c)) e = .ok (v.shiftLvl c)) ∧
    (∀ {unf c f a v}, vapp n unf f a = .ok v →
      vapp n unf (f.shiftLvl c) (a.shiftLvl c) = .ok (v.shiftLvl c)) := sorry
theorem eval_shiftLvl {n unf c ρ e v}
    (h : eval n unf ρ e = .ok v) :
    eval n unf (ρ.map (Val.shiftLvl c)) e = .ok (v.shiftLvl c) := sorry
theorem vapp_shiftLvl {n unf c f a v}
    (h : vapp n unf f a = .ok v) :
    vapp n unf (f.shiftLvl c) (a.shiftLvl c) = .ok (v.shiftLvl c) := sorry
theorem Closure.envLevelsBelow_take
    {d : Nat} {env : List Val} (h : Closure.envLevelsBelow d env) (n : Nat) :
    Closure.envLevelsBelow d (env.take n) := sorry
theorem Closure.envFullyQuotable_take
    {d : Nat} {env : List Val} (h : Closure.envFullyQuotable d env) (n : Nat) :
    Closure.envFullyQuotable d (env.take n) := sorry
theorem Closure.envFullyQuotable_getElem?
    {d : Nat} {env : List Val} (h : Closure.envFullyQuotable d env)
    {k : Nat} {v : Val} (hk : env[k]? = some v) :
    Val.fullyQuotable d v ∧ ∃ qe, quote fuelω d v = .ok qe := sorry
theorem eval_vapp_levelsBelow :
    ∀ n,
    (∀ {unf d ρ e v}, eval n unf ρ e = .ok v →
      Closure.envLevelsBelow d ρ → Val.levelsBelow d v) ∧
    (∀ {unf d f a v}, vapp n unf f a = .ok v →
      Val.levelsBelow d f → Val.levelsBelow d a → Val.levelsBelow d v) := sorry
theorem eval_levelsBelow {n unf d ρ e v}
    (h : eval n unf ρ e = .ok v) (hρ : Closure.envLevelsBelow d ρ) :
    Val.levelsBelow d v := sorry
theorem eval_vapp_preserves_fullyQuotable :
    ∀ n,
    (∀ {unf d ρ e v}, eval n unf ρ e = .ok v →
      Closure.envFullyQuotable d ρ →
      e.closedAt ρ.length = true →
      Val.fullyQuotable d v) ∧
    (∀ {unf d f a v}, vapp n unf f a = .ok v →
      Val.fullyQuotable d f → Val.fullyQuotable d a →
      (∃ qf, quote fuelω d f = .ok qf) →
      (∃ qa, quote fuelω d a = .ok qa) →
      Val.fullyQuotable d v) := sorry
theorem eval_preserves_fullyQuotable {n unf d ρ e v}
    (heval : eval n unf ρ e = .ok v)
    (hρ : Closure.envFullyQuotable d ρ)
    (hcl : e.closedAt ρ.length = true) :
    Val.fullyQuotable d v := sorry
theorem Closure.envFullyQuotable_of_getElem? {d : Nat} {ρ : List Val}
    (hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
           ∃ qe, quote fuelω d v = .ok qe)
    (hρfq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
            Val.fullyQuotable d v) :
    Closure.envFullyQuotable d ρ := sorry
mutual
/-- Monotonicity of levelsBelow/envLevelsBelow. -/
theorem Val.levelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ v, Val.levelsBelow d v → Val.levelsBelow d' v := sorry
theorem Neutral.levelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ n, Neutral.levelsBelow d n → Neutral.levelsBelow d' n := sorry
theorem Closure.levelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ cl, Closure.levelsBelow d cl → Closure.levelsBelow d' cl := sorry
theorem Closure.envLevelsBelow_mono {d d' : Nat} (hle : d ≤ d') :
    ∀ env, Closure.envLevelsBelow d env →
           Closure.envLevelsBelow d' env := sorry
end

/-!
### Cutoff-parametrised depth shift for `quote`

A one-step quote-depth-shift, but generalised with a cutoff `c`
on the expression-level shift so the closure case's body
(recursing one binder deeper) can cleanly pass a larger cutoff.

At `c = 0`: the Val shift `v.shiftLvl (d-0) = v.shiftLvl d` is a
no-op whenever `v.levelsBelow d` holds (true for any `v` coming
out of a successful `quote n d v = .ok _`), so the shape reduces
to `quote (d+1) v = .ok (e.shift 1 0)` — the existing
`quote_depth_shift`.

At `c+1` (used inside the closure body, one binder deeper): the
recursive IH supplies `quote (d+2) (v.shiftLvl (d-c)) =
some (e.shift 1 (c+1))`, exactly matching the post-`eval_shiftLvl`
body state.

Proof is by induction on fuel, combined over the three quote
families. -/
theorem quote_quoteClosure_quoteNeutral_depth_shift :
    ∀ n,
    (∀ {c d v e}, c ≤ d → quote n d v = .ok e →
        quote n (d+1) (v.shiftLvl (d-c)) = .ok (e.shift 1 c)) ∧
    (∀ {c d cl e}, c ≤ d → quoteClosure n d cl = .ok e →
        quoteClosure n (d+1) (cl.shiftLvl (d-c))
          = .ok (e.shift 1 (c+1))) ∧
    (∀ {c d ne e}, c ≤ d → quoteNeutral n d ne = .ok e →
        quoteNeutral n (d+1) (ne.shiftLvl (d-c))
          = .ok (e.shift 1 c)) := sorry
theorem quote_depth_shift_of_levelsBelow {fuel d v e}
    (hlvl : Val.levelsBelow d v)
    (hq : quote fuel d v = .ok e) :
    quote fuel (d+1) v = .ok (e.shift 1 0) := sorry
theorem quote_depth_shift {d v e}
    (hlvl : Val.levelsBelow d v)
    (hq : quote fuelω d v = .ok e) :
    quote fuelω (d + 1) v = .ok (e.shift 1 0) := sorry
theorem quote_depth_shift_n {k d v e}
    (hlvl : Val.levelsBelow k v)
    (hle : k ≤ d) (hq : quote fuelω k v = .ok e) :
    quote fuelω d v = .ok (e.shift (d - k) 0) := sorry
mutual
theorem Val.levelsBelow_of_fullyQuotable : ∀ (d : Nat) (v : Val),
    Val.fullyQuotable d v → Val.levelsBelow d v := sorry
theorem Neutral.levelsBelow_of_fullyQuotable : ∀ (d : Nat) (n : Neutral),
    Neutral.fullyQuotable d n → Neutral.levelsBelow d n := sorry
theorem Closure.levelsBelow_of_fullyQuotable : ∀ (d : Nat) (cl : Closure),
    Closure.fullyQuotable d cl → Closure.levelsBelow d cl := sorry
theorem Closure.envLevelsBelow_of_envFullyQuotable : ∀ (d : Nat) (env : List Val),
    Closure.envFullyQuotable d env → Closure.envLevelsBelow d env := sorry
end

-- Monotonicity of fullyQuotable in depth: a Val fully-quotable at d
-- is also fully-quotable at any d' ≥ d. Quote witnesses at d' are
-- derived from witnesses at d via quote_depth_shift_n. Moved here
-- (before R_depth_lift) 2026-04-22 for Tier 0 refactor.
mutual
theorem Val.fullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (v : Val), Val.fullyQuotable d v → Val.fullyQuotable d' v := sorry
theorem Neutral.fullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (n : Neutral), Neutral.fullyQuotable d n → Neutral.fullyQuotable d' n := sorry
theorem Closure.fullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (cl : Closure), Closure.fullyQuotable d cl → Closure.fullyQuotable d' cl := sorry
theorem Closure.envFullyQuotable_mono : ∀ {d d' : Nat}, d ≤ d' →
    ∀ (env : List Val), Closure.envFullyQuotable d env →
      Closure.envFullyQuotable d' env := sorry
end

mutual

/-- **Depth-lift of R** with `Val.levelsBelow d v` side
condition. After the R/Equiv_c refactor (commit b5f0fd8), R's
clauses carry `Equiv_c d`, which admits a `shift` to `Equiv_c (d+1)`
without any closedness assumption.

Cases:
- `.type`/`.neutral`: base conjunct `∀ qe' hq', Equiv_c d qe' e`.
  At d+1, quote produces `qe'.shift 1 0` via `quote_depth_shift`,
  and `Equiv_c.shift` lifts `Equiv_c d qe' e` to
  `Equiv_c (d+1) (qe'.shift 1 0) (e.shift 1 0)`.
- `.lam`/`.iota`/`.fix`: env-exposes existentials lift via recursion
  on the head `R` (smaller `sizeOf v`), `RList_depth_lift` for the
  body env, and `Equiv_c.shift` for the final conjunct — modulo
  a substEnv-shift commutation lemma to match the target shape
  (currently still sorry for closure cases; see helper below). -/
theorem R_depth_lift {n d v e}
    {qe : Expr} (hlvl : Val.levelsBelow d v)
    (hfq : Val.fullyQuotable d v)
    (hq : quote fuelω d v = .ok qe)
    (h : R n d v e) :
    R n (d + 1) v (e.shift 1 0) := sorry
theorem RList_depth_lift {n d ρ ρe}
    (hlvl : Closure.envLevelsBelow d ρ)
    (hfq : Closure.envFullyQuotable d ρ)
    (h : RList n d ρ ρe) :
    RList n (d + 1) ρ (ρe.map (·.shift 1 0)) := sorry
end

/-- A fresh `.var d` realises `.bvar 0` at depth `d+1`. -/
theorem R_fresh_bvar0 (n d : Nat) :
    R n (d + 1) (.neutral (.var d)) (.bvar 0) := sorry
theorem REnv_depth_lift {n d ρ ρe}
    (henv : REnv n d ρ ρe)
    (hquotes : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → ∃ qe, quote fuelω d v = .ok qe)
    (hρlvl : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.levelsBelow d v)
    (hρfq : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.fullyQuotable d v) :
    REnv n (d + 1) ρ (ρe.map (·.shift 1 0)) := sorry
theorem REnv_lift {n d ρ ρe}
    (henv : REnv n d ρ ρe)
    (hquotes : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → ∃ qe, quote fuelω d v = .ok qe)
    (hρlvl : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.levelsBelow d v)
    (hρfq : ∀ (k : Nat) (v : Val),
        ρ[k]? = some v → Val.fullyQuotable d v) :
    REnv n (d + 1)
      (Val.neutral (.var d) :: ρ)
      (.bvar 0 :: ρe.map (·.shift 1 0)) := sorry
private theorem List.take_eq_of_agree {α} {ρ₁ ρ₂ : List α} {j : Nat}
    (hagree : ∀ k, k < j → ρ₁[k]? = ρ₂[k]?) :
    ρ₁.take j = ρ₂.take j := sorry
theorem eval_env_agree :
    ∀ {fuel unf : Nat} {body : Expr} {ρ₁ ρ₂ : Env},
      (∀ k, k < bvarBound body → ρ₁[k]? = ρ₂[k]?) →
      eval fuel unf ρ₁ body = eval fuel unf ρ₂ body := sorry
theorem eval_env_take {fuel unf : Nat} {ρ : Env} {body : Expr} :
    eval fuel unf (ρ.take (bvarBound body)) body
      = eval fuel unf ρ body := sorry
theorem Equiv.beta (dom body arg : Expr) :
    Equiv (.app (.lam dom body) arg) (body.subst 0 arg) := sorry
theorem Equiv.fix_unfold (ann body : Expr) :
    Equiv (.fix ann body) (body.subst 0 (.fix ann body)) := sorry
theorem Equiv.iota_unfold (ann body : Expr) :
    Equiv (.iota ann body) (body.subst 0 (.iota ann body)) := sorry
theorem REnv_cons {n d ρ ρe v e}
    (henv : REnv n d ρ ρe) (hv : R n d v e) :
    REnv n d (v :: ρ) (e :: ρe) := sorry
private theorem closure_clause_witness {k d ρ ρe} {bExpr : Expr}
    (henv : REnv (k+1) d ρ ρe)
    (hclb_full : bExpr.closedAt (ρe.length + 1) = true) :
    let j := bvarBound bExpr - 1
    let ρe' := ρe.take j
    RList (k+1) d (ρ.take j) ρe' ∧
    bExpr.closedAt (ρe'.length + 1) = true ∧
    bExpr.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))
      = bExpr.substEnv (.bvar 0 :: ρe.map (·.shift 1 0)) := sorry
private theorem R_neutral_app {k d N fe ae}
    (hdecomp : ∀ e', quote fuelω d (.neutral N) = .ok e' →
       ∃ ne ve, e' = .app ne ve ∧
         Equiv_c d ne fe ∧ Equiv_c d ve ae) :
    R (k+1) d (Val.neutral N) (.app fe ae) := sorry
theorem quoteClosure_realises {d : Nat} {cl : Closure} {body' : Expr}
    {m : Nat} {ρe' : List Expr}
    (_hq : quoteClosure fuelω d cl = .ok body')
    (_hRL : RList m d cl.env ρe')
    (_hclb : cl.body.closedAt (ρe'.length + 1) = true)
    (_hlvl : Closure.envLevelsBelow d cl.env)
    (_hfq : Closure.envFullyQuotable d cl.env) :
    Equiv_c (d+1) body'
      (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0))) := sorry
theorem R_quote_equiv {n d v e}
    (hn : 0 < n) (h : R n d v e)
    {e' : Expr} (hq : quote fuelω d v = .ok e') :
    Equiv_c d e' e := sorry
private theorem quote_stuckRec_decomp {d vf va} (e' : Expr)
    (hq : quote fuelω d (.neutral (.stuckRec vf va)) = .ok e') :
    ∃ ne ve, e' = .app ne ve ∧
      quote fuelω d vf = .ok ne ∧ quote fuelω d va = .ok ve := sorry
mutual
/-- Realisation through `vapp`. Mutual with `eval_realises`
on `fuel`; both stay at the *same* step-index `m`
throughout (the env-exposes `R` clause makes the Kripke
step-loss disappear — see `R`'s docstring).

`.neutral`/`.type`/stuck heads: `r` is `.neutral …`; base
via `Equiv.app` on the inputs' base conjuncts.

`.lam` head: `r = eval fuel (va :: cl.env) cl.body`. From
`hRf`'s clause obtain `RList m d cl.env ρe'`, cons `hRa` to
get `REnv m d (va :: cl.env) (ae :: ρe')`, apply
`eval_realises` (mutual, fuel `< fuel+1`), then
`R_resp_Equiv` along `.app fe ae ≡ bode.subst 0 ae` (via
`Equiv.beta` after `heqL`) `= cl.body.substEnv (ae :: ρe')`
(via `substEnv_subst_comp`).

`.iota`/`.fix` head, unfold branch: first
`f' = eval fuel (vf :: cl.env) cl.body`, then
`r = vapp fuel f' va`. From `hRf`'s clause + `REnv_cons hRf`
(self-binding) + `eval_realises` (mutual): `R m d f'
(cl.body.substEnv (fe :: ρe')) = bode.subst 0 fe`. Then
`R_resp_Equiv` along `bode.subst 0 fe ≡ fe` (via
`Equiv.subst_resp heqI` + `Equiv.iota_unfold` + `heqI⁻¹`)
gives `R m d f' fe`. Recurse `vapp_realises` (mutual,
fuel `< fuel+1`).

The `bode.subst 0 fe ≡ fe` step requires `Equiv.subst_resp`
on `fe ≡ .iota/.fix anne bode`, which was deleted
2026-04-21 (it depended on `Equiv.shift`'s nil-Γ sorry).
The closedness-carrying `Equiv.subst_resp_closed` is
available but needs `fe.closedAt 0 ∧ anne.closedAt 0`,
which don't hold in open contexts. Hence these two unfold
sub-sorries remain — they close once either (a) a general
closedness invariant is threaded through `vapp_realises`,
or (b) the nil-Γ `Equiv.shift` sorry is closed (e.g. via
`Subtype'.shift_nil` with `Seen.wellClosed`). -/
theorem vapp_realises {fuel unf vf va r m d fe ae}
    (hvapp : vapp fuel unf vf va = .ok r)
    (hRf : R m d vf fe) (hRa : R m d va ae) :
    R m d r (.app fe ae) := sorry
theorem eval_realises {fuel unf : Nat} {ρ : Env} {body : Expr} {v : Val}
    (heval : eval fuel unf ρ body = .ok v)
    {m d : Nat} {ρe : List Expr}
    (henv : REnv m d ρ ρe)
    (henvLvl : Closure.envLevelsBelow d ρ)
    (henvFq : Closure.envFullyQuotable d ρ)
    (hcl : body.closedAt ρe.length = true) :
    R m d v (body.substEnv ρe) := sorry
end

/-- A fresh neutral at level `lvl < d` quotes to `bvar
(d-1-lvl)`. Forward direction; the inversion is
`quoteNeutral_var` below. -/
private theorem quote_neutral_var_fwd {d lvl : Nat} (hlt : lvl < d) :
    quote fuelω d (.neutral (.var lvl)) = .ok (.bvar (d - 1 - lvl)) := sorry
theorem R_lam_clause {n d dom cl ea}
    (hR : R (n+1) d (.lam dom cl) ea) :
    ∃ ρe' dome,
      R (n+1) d dom dome ∧
      RList (n+1) d cl.env ρe' ∧
      cl.body.closedAt (ρe'.length + 1) = true ∧
      Closure.envLevelsBelow d cl.env ∧
      Closure.envFullyQuotable d cl.env ∧
      Equiv_c d ea (.lam dome
        (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) := sorry
theorem R_iota_clause {n d ann cl ea}
    (hR : R (n+1) d (.iota ann cl) ea) :
    ∃ ρe' anne,
      R (n+1) d ann anne ∧
      RList (n+1) d cl.env ρe' ∧
      cl.body.closedAt (ρe'.length + 1) = true ∧
      Closure.envLevelsBelow d cl.env ∧
      Closure.envFullyQuotable d cl.env ∧
      Equiv_c d ea (.iota anne
        (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) := sorry
theorem R_fix_clause {n d ann cl ea}
    (hR : R (n+1) d (.«fix» ann cl) ea) :
    ∃ ρe' anne,
      R (n+1) d ann anne ∧
      RList (n+1) d cl.env ρe' ∧
      cl.body.closedAt (ρe'.length + 1) = true ∧
      Closure.envLevelsBelow d cl.env ∧
      Closure.envFullyQuotable d cl.env ∧
      Equiv_c d ea (.fix anne
        (cl.body.substEnv (.bvar 0 :: ρe'.map (·.shift 1 0)))) := sorry
private theorem fuelω_succ : fuelω = (fuelω - 1) + 1 := sorry
theorem quote_type {d : Nat} : quote fuelω d .type = .ok .type := sorry
theorem quote_bot {d : Nat} : quote fuelω d .bot = .ok .bot := sorry
theorem quote_neutral {d : Nat} {n : Neutral} {e : Expr}
    (h : quote fuelω d (.neutral n) = .ok e) :
    quoteNeutral (fuelω - 1) d n = .ok e := sorry
theorem quoteNeutral_var {d k : Nat} {e : Expr}
    (h : quoteNeutral fuelω d (.var k) = .ok e) :
    k < d ∧ e = .bvar (d - 1 - k) := sorry
theorem quoteNeutral_app {d : Nat} {n : Neutral} {v : Val} {e : Expr}
    (h : quoteNeutral fuelω d (.app n v) = .ok e) :
    ∃ ne ve, quoteNeutral (fuelω - 1) d n = .ok ne ∧
             quote (fuelω - 1) d v = .ok ve ∧
             e = .app ne ve := sorry
theorem quoteNeutral_stuckRec {d : Nat} {f a : Val} {e : Expr}
    (h : quoteNeutral fuelω d (.stuckRec f a) = .ok e) :
    ∃ fe ae, quote (fuelω - 1) d f = .ok fe ∧
             quote (fuelω - 1) d a = .ok ae ∧
             e = .app fe ae := sorry
theorem quoteNeutralω {d : Nat} {n : Neutral} {e : Expr}
    (h : quoteNeutral (fuelω - 1) d n = .ok e) :
    quoteNeutral fuelω d n = .ok e := sorry
theorem quoteω {d : Nat} {v : Val} {e : Expr}
    (h : quote (fuelω - 1) d v = .ok e) :
    quote fuelω d v = .ok e := sorry
theorem quoteClosureω {d : Nat} {cl : Closure} {e : Expr}
    (h : quoteClosure (fuelω - 1) d cl = .ok e) :
    quoteClosure fuelω d cl = .ok e := sorry
theorem quote_quoteClosure_quoteNeutral_closedAt :
    ∀ n,
    (∀ {d v e}, quote n d v = .ok e → e.closedAt d = true) ∧
    (∀ {d cl e}, quoteClosure n d cl = .ok e → e.closedAt (d+1) = true) ∧
    (∀ {d ne e}, quoteNeutral n d ne = .ok e → e.closedAt d = true) := sorry
theorem quote_closedAt {fuel d v e} (h : quote fuel d v = .ok e) :
    e.closedAt d = true := sorry
theorem quoteClosure_closedAt {fuel d cl e}
    (h : quoteClosure fuel d cl = .ok e) :
    e.closedAt (d+1) = true := sorry
theorem quoteNeutral_closedAt {fuel d ne e}
    (h : quoteNeutral fuel d ne = .ok e) :
    e.closedAt d = true := sorry
theorem quote_lam {d : Nat} {dom : Val} {cl : Closure} {e : Expr}
    (h : quote fuelω d (.lam dom cl) = .ok e) :
    ∃ dome bodye,
      quote (fuelω - 1) d dom = .ok dome ∧
      quoteClosure (fuelω - 1) d cl = .ok bodye ∧
      e = .lam dome bodye := sorry
theorem quote_iota {d : Nat} {ann : Val} {cl : Closure} {e : Expr}
    (h : quote fuelω d (.iota ann cl) = .ok e) :
    ∃ anne bodye,
      quote (fuelω - 1) d ann = .ok anne ∧
      quoteClosure (fuelω - 1) d cl = .ok bodye ∧
      e = .iota anne bodye := sorry
theorem quote_fix {d : Nat} {ann : Val} {cl : Closure} {e : Expr}
    (h : quote fuelω d (.«fix» ann cl) = .ok e) :
    ∃ anne bodye,
      quote (fuelω - 1) d ann = .ok anne ∧
      quoteClosure (fuelω - 1) d cl = .ok bodye ∧
      e = .«fix» anne bodye := sorry
abbrev QuotesSeen (S : List (Val × Val)) (Γ : TyCtx) (Se : Seen) : Prop :=
  ∀ p ∈ S, ∃ pe ∈ Se,
    pe.1 ≤ Γ.size ∧
    quote fuelω pe.1 p.1 = .ok pe.2.1 ∧
    quote fuelω pe.1 p.2 = .ok pe.2.2

/-- The type context quotes into `Γe` at matching de Bruijn
indices. `Γ` is level-indexed (`Γ[k]` = type of `.var k`);
`Γe` is index-indexed (`Γe[i]` = type of `.bvar i`). The
quote depth is `k`: entry `k` was *added* when `Γ` had size
`k`, so its Val's neutrals reference levels `0..k-1` and
should quote at depth `k` (not `k+1`) to land in the right
`Γe`-relative slot. (`tyCheck_sound_open`'s `.lam` arm is
the witness — `Subtype'.lam` extends `Γe` with `domB` at
index 0, and `domB` is `quote |Γ| domV`.)

The `Γ.size = Γe.length` conjunct is the length invariant
that `OpenCtx.hlen` maintains at the top level. Making it
explicit in `QuotesCtx` lets the `.hyp` case of
`SubN_to_Subtype'` rewrite between the motive's `Γ.size`
shift amount and `Subtype'.hyp`'s `Γe.length` shift amount. -/
abbrev QuotesCtx (Γ : TyCtx) (Γe : Ctx) : Prop :=
  Γ.size = Γe.length ∧
  (∀ k τ, Γ[k]? = some τ →
    ∃ τe, Γe.get? (Γ.size - 1 - k) = some τe ∧
          quote fuelω k τ = .ok τe) ∧
  (∀ k τ, Γ[k]? = some τ → Val.levelsBelow k τ)

/-!
### The mutual bridge

Three theorems proven by simultaneous structural recursion
on `SubV`/`SubN`/`SynthN`, using the joint recursor
`SubV.rec`. Each motive packages the quote hypotheses; the
recursor supplies one IH per recursive premise.
-/

-- `SubN_to_Subtype'` and `SynthN_to_Subtype'` deleted
-- 2026-04-21. Both were sorry-ridden (each case of their
-- joint-recursor application required tier-2 realisability
-- threading that's not yet built); their only external
-- consumer (`SubV_to_Subtype'.neutral_struct`) now sorries
-- inline. Future work: re-derive via a proper `MR`-augmented
-- motive that carries realisability + quote-totality
-- hypotheses.

-- `SubV_to_Subtype'` deleted 2026-04-21: 11/15 cases were sorried
-- (closure-opening + neutral_ascent). Its only caller
-- (`subCheckVal_sound_open`) also deleted; downstream callers
-- (tyCheck_sound_open etc.) now sorry the subtype derivation
-- directly. Future work: re-derive via `MR`-augmented motive
-- carrying realisability hypotheses.

/-!
## Open-context `tyCheck`/`tyInfer` soundness

`tyCheck_sound_closed` (Soundness.lean) is at `Γ = #[]`/`ρ = []`/
`Γe = []`. Its `.lam`/`.letE` arms recurse at non-empty `Γ`,
which the closed IH cannot reach. The open generalisation
here threads a context-bundle `OpenCtx Γ ρ Γe` through the
mutual induction; the closed forms in `Soundness.lean`
specialise it at `OpenCtx.empty`.

**Statement shape.** The expected type comes as `(τV : Val)`
plus its quote `(τe, hqτ)`, *not* a source `(τ : Expr)` with
`eval τ = τV`. This is because the recursive cases (`.letE`'s
binder type from `letBinderType`; `tyInfer`'s result) supply
a `Val` directly with no source `Expr` to point at. The
closed wrapper does `eval [] τ → τV` then bridges `τe ≡ τ`
via `eval_quote_equiv_closed`.

**Conclusion.** `Subtype' [] Γe e τe` — the source `e` (open,
with bvars into `Γe`) is below the *quoted* expected type at
the declarative context. The seen-set is always `[]` since
`tyCheck`'s `subCheckVal` calls start at empty seen.
-/

-- `subCheckVal_sound_open` deleted 2026-04-21 along with
-- `SubV_to_Subtype'`. Callers (in tyCheck_sound_open's mutual)
-- now sorry the derivation directly — a net declaration-sorry
-- reduction since SubV_to_Subtype's warning disappears.

/-- The open-context invariant for `tyCheck`/`tyInfer`
soundness. Carries an explicit Expr-level substitution
`ρe` realised by the runtime `ρ` (via `REnv`), so the
conclusion can be stated as `Subtype' [] Γe (e.substEnv
ρe) τe` — which is *correct* for both fresh-neutral and
let-bound `ρ` entries (the previous `Equiv e' e at Γe`
form was false for the latter; see `push_let`).

  - `hΓ` for `subCheckVal_sound_open`;
  - `hρq` for `REnv_depth_lift` and `R_depth_lift` (each
    `ρ` entry quotes at the current depth);
  - `henv` (replacing the ad-hoc `hρeq`) packages the
    realisation; the eval-quote-equiv property is
    *derived* below as `OpenCtx.eq`. -/
structure OpenCtx (Γ : TyCtx) (ρ : Env) (Γe : Ctx)
    (ρe : List Expr) : Prop where
  hΓ : QuotesCtx Γ Γe
  hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
        ∃ we, quote fuelω Γ.size v = .ok we
  /-- Levelbound invariant: every entry of `ρ` has neutral-var
  levels `< Γ.size`. Maintained by `push_fresh` (new head
  `.var Γ.size` has level `Γ.size < Γ.size+1`) and by
  `push_let` (new head `valV` from `eval ρ val` has levels
  `< Γ.size` by `eval_levelsBelow`, then `< Γ.size+1` by mono).
  Used by `quote_depth_shift` at call sites (via
  `hρlvl_lift`). -/
  hρlvl : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
          Val.levelsBelow Γ.size v
  /-- Closedness of substituted-environment entries. Each
  `ρe[k]` is `closedAt Γ.size` — it has no free bvars beyond
  the current depth. Maintained by `empty` (vacuous), `push_fresh`
  (head `.bvar 0` closedAt 1 ≤ Γ.size+1; tail entries shift
  `closedAt Γ.size → closedAt Γ.size+1`), and `push_let` (head
  `val.substEnv ρe` closedAt Γ.size from `val.closedAt ρe.length`
  + tail entries closedAt Γ.size; then shift to Γ.size+1).
  This invariant is Path A's enabler: with it, shifts of ρe
  entries at cutoff 0 lift to closedAt Γ.size+1, and downstream
  closedness-carrying Equiv.shift variants can fire. -/
  hρecl : ∀ (k : Nat) (e : Expr), ρe[k]? = some e →
          e.closedAt Γ.size = true
  /-- Recursive full quotability for each ρ entry. -/
  hρfq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
         Val.fullyQuotable Γ.size v
  henv : REnv 1 Γ.size ρ ρe
  /-- All four contexts grow in lockstep (`empty` starts at
  0; both `push_*` add 1 to each). `tyInfer_sound_open .bvar`
  needs this to turn `hcl : k < ρe.length` into `k < Γ.size`
  for the level↔index arithmetic. -/
  hlen : Γ.size = ρe.length
  /-- Each substituted entry has its declared context type:
  `ρe[k] ⊑ Γe[k].shift (k+1) 0`. This is `Subtype'.bvar`'s
  conclusion, generalised from `.bvar k` to whatever `ρe[k]`
  realises it. `tyInfer_sound_open .bvar` reads this
  directly. `push_fresh` discharges `k=0` via `Subtype'.bvar`
  (the head IS `.bvar 0`); `push_let` via the caller's
  `hval_le` (the let-bound value's typing). The `k>0` tail
  lifts via `ctx_extend [head]`. -/
  hwf : ∀ k w τe, ρe[k]? = some w → Γe.get? k = some τe →
        Subtype' [] Γe w (τe.shift (k+1) 0)

/-- Derived eval-quote-equiv: evaluating `e` under `ρ` and
quoting gives something `Equiv` to `e.substEnv ρe`. This
is the open form of `eval_quote_equiv_closed`. -/
theorem OpenCtx.eq {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (heval : eval fuel unf ρ e = .ok v)
    (hcl : e.closedAt ρe.length = true)
    {e'} (hq : quote fuelω Γ.size v = .ok e') :
    Subtype' [] Γe e' (e.substEnv ρe) ∧
    Subtype' [] Γe (e.substEnv ρe) e' := sorry
theorem OpenCtx.empty : OpenCtx #[] [] [] [] := sorry
theorem eval_quotable_open {fuel unf d : Nat} {ρ : Env}
    {e : Expr} {v : Val}
    (hfuel : fuel ≤ fuelω)
    (hnfq : ((eval fuelω unf ρ e) >>= (quote fuelω d)).isOk)
    (heval : eval fuel unf ρ e = .ok v) :
    ∃ ve, quote fuelω d v = .ok ve := sorry
theorem OpenCtx.eval_quotes' {Γ ρ Γe ρe} (_hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf e v} (hfuel : fuel ≤ fuelω)
    (hnfq : ((eval fuelω unf ρ e) >>= (quote fuelω Γ.size)).isOk)
    (heval : eval fuel unf ρ e = .ok v) :
    ∃ ve, quote fuelω Γ.size v = .ok ve := sorry
private theorem hwf_lift_tail {Γe : Ctx} {ρe : List Expr}
    (hwf : ∀ k w τe, ρe[k]? = some w → Γe.get? k = some τe →
           Subtype' [] Γe w (τe.shift (k+1) 0))
    (head : Expr) :
    ∀ m w τe,
      (ρe.map (·.shift 1 0))[m]? = some w →
      Γe.get? m = some τe →
      Subtype' [] (head :: Γe) w (τe.shift (m+2) 0) := sorry
private theorem hρq_lift {d : Nat} {ρ : Env}
    (hρq : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
           ∃ we, quote fuelω d v = .ok we)
    (hρlvl : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
             Val.levelsBelow d v) :
    ∀ (k : Nat) (v : Val), ρ[k]? = some v →
    ∃ we, quote fuelω (d + 1) v = .ok we := sorry
private theorem hρlvl_lift {d : Nat} {ρ : Env}
    (hρlvl : ∀ (k : Nat) (v : Val), ρ[k]? = some v →
             Val.levelsBelow d v) :
    ∀ (k : Nat) (v : Val), ρ[k]? = some v →
    Val.levelsBelow (d + 1) v := sorry
theorem QuotesCtx.push {Γ : TyCtx} {Γe : Ctx}
    (hΓ : QuotesCtx Γ Γe)
    {τ : Val} {τe : Expr}
    (hqτ : quote fuelω Γ.size τ = .ok τe)
    (hτlvl : Val.levelsBelow Γ.size τ) :
    QuotesCtx (Γ.push τ) (τe :: Γe) := sorry
theorem OpenCtx.push_fresh {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {τ : Val} {τe : Expr}
    (hqτ : quote fuelω Γ.size τ = .ok τe)
    (hτlvl : Val.levelsBelow Γ.size τ) :
    OpenCtx (Γ.push τ) (.neutral (.var Γ.size) :: ρ)
            (τe :: Γe) (.bvar 0 :: ρe.map (·.shift 1 0)) := sorry
theorem OpenCtx.push_let {Γ ρ Γe ρe} (hctx : OpenCtx Γ ρ Γe ρe)
    {fuel unf : Nat} (hfuel : fuel ≤ fuelω)
    {val : Expr} {valV valTy : Val} {valTye : Expr}
    (hev : eval fuel unf ρ val = .ok valV)
    (hnfq : ((eval fuelω unf ρ val) >>= (quote fuelω Γ.size)).isOk)
    (hclv : val.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size valTy = .ok valTye)
    (hτlvl : Val.levelsBelow Γ.size valTy)
    (hval_le : Subtype' [] Γe (val.substEnv ρe) valTye) :
    OpenCtx (Γ.push valTy) (valV :: ρ)
            (valTye :: Γe)
            ((val.substEnv ρe).shift 1 0
              :: ρe.map (·.shift 1 0)) := sorry
mutual

/-- Open-context `tyInfer` soundness. The conclusion bundles
quote-existence so callers (the `tyCheckFallback` arm) don't
need a separate quote-totality side-lemma.

**Note on `.fix`/`.iota` (A9)**: `tyInfer` returns the bare
annotation, which is *not* sound (`(.fix Nat_ unit_) ⋢
Nat_`). This case is therefore unprovable as stated. The
mitigation: every *caller* of `tyInfer` that needs a
verified type goes through `tyCheck`'s `.fix`/`.iota` arm or
`letBinderType` (both of which verify); `tyCheckFallback`'s
`some`-path is the only direct consumer of an unverified
`tyInfer` result, and *that* path is exactly the residual
A9 hole the verifier-on-`c5914db` flagged for `.app`-chains
with bad-fix heads. So `tyInfer_sound_open` below carries
an additional hypothesis `(hwf : <e contains no ill-formed
fix/ι>)` *or* the `.fix`/`.iota` arm is sorried with this
note — taking the latter for now. -/
theorem tyInfer_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {e : Expr} {τV : Val}
    (hcl : e.closedAt ρe.length = true)
    (h : tyInfer fuel Γ ρ e = .ok (some τV)) :
    ∃ τe, quote fuelω Γ.size τV = .ok τe ∧
          Subtype' [] Γe (e.substEnv ρe) τe := sorry
theorem tyCheckFallback_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {e : Expr} {τV : Val} {τe : Expr}
    (hcl : e.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size τV = .ok τe)
    (h : tyCheckFallback fuel Γ ρ e τV = .ok true) :
    Subtype' [] Γe (e.substEnv ρe) τe := sorry
theorem tyCheck_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {e : Expr} {τV : Val} {τe : Expr}
    (hcl : e.closedAt ρe.length = true)
    (hqτ : quote fuelω Γ.size τV = .ok τe)
    (h : tyCheck fuel Γ ρ e τV = .ok true) :
    Subtype' [] Γe (e.substEnv ρe) τe := sorry
theorem letBinderType_sound_open
    {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {Γ : TyCtx} {ρ : Env} {Γe : Ctx} {ρe : List Expr}
    (hctx : OpenCtx Γ ρ Γe ρe)
    {val : Expr} {valV valTy : Val}
    (hnfq : ((eval fuelω unfBound ρ val) >>= (quote fuelω Γ.size)).isOk)
    (hcl : val.closedAt ρe.length = true)
    (h : letBinderType fuel Γ ρ val = .ok (valV, valTy)) :
    eval fuel unfBound ρ val = .ok valV ∧
    ∃ valTye, quote fuelω Γ.size valTy = .ok valTye ∧
              Subtype' [] Γe (val.substEnv ρe) valTye := sorry
end

/-- The closed forms in `Soundness.lean` derive from the
open ones at the empty context (`ρe = []`,
`substEnv_nil`). The `hcl0` precondition is the
well-scopedness of `e`. -/
example {fuel : Nat} (hfuel : fuel ≤ fuelω)
    {e : Expr} {τV : Val} {τe : Expr}
    (hcl0 : e.closedAt 0 = true)
    (hqτ : quote fuelω 0 τV = .ok τe)
    (h : tyCheck fuel #[] [] e τV = .ok true) :
    Subtype' [] [] e τe := by
  have := tyCheck_sound_open hfuel OpenCtx.empty
    (by simpa using hcl0) (by simpa using hqτ) h
  simpa [Expr.substEnv_nil] using this

end NbE
