import PSS.Sub

open Expr PSS

-- EXPERIMENT: Can we prove top_not_sub_headForm using a DIFFERENT proof structure?
-- Key idea: use mutual strong induction on (h.height + total_wf_weight(h))
-- where total_wf_weight sums up all Wf heights embedded in the Sub derivation.

-- First, let's define total weight:
mutual
def Sub.totalWeight : Sub Γ a b → Nat
  | .refl _       => 0
  | .top _        => 0
  | .trans h1 h2 hw => 1 + h1.totalWeight + h2.totalWeight + hw.totalWeight
  | .bvar _       => 0
  | .lam h1 h2 h3  => 1 + h1.totalWeight + h2.totalWeight + h3.totalWeight
  | .app_cong h1 h2 h3 => 1 + h1.totalWeight + h2.totalWeight + h3.totalWeight
  | .beta_L       => 0
  | .beta_R       => 0

def Wf.totalWeight : Wf Γ e → Nat
  | .var _         => 0
  | .top           => 0
  | .lam hd hb     => 1 + hd.totalWeight + hb.totalWeight
  | .app hf ha hs hsub harg => 1 + hf.totalWeight + ha.totalWeight + hs.totalWeight + hsub.totalWeight + harg.totalWeight
end

-- totalWeight includes the full recursive weight of all Sub and Wf terms.
-- For trans h1 h2 hw: weight = 1 + w(h1) + w(h2) + w(hw)
-- w(hw) includes the weights of Sub derivations INSIDE hw.

-- The key question: in the app_cong composition, does totalWeight decrease?

-- Original: h1g = trans h1a h1b hw1 (where h1b will be further decomposed)
-- w(h1g) = 1 + w(h1a) + w(h1b) + w(hw1)
-- After h1bHelper peels off trans layers and reaches h1b_g = app_cong hf ha ha':
-- h1a' = (accumulated), h1b_g = app_cong, hw1' = (accumulated or original)
-- The composition: trans h1a' (app_cong hf ha ha') hw1'
-- w(composition) = 1 + w(h1a') + w(app_cong) + w(hw1')

-- But the original h1g.totalWeight included w(h1b) which included w(app_cong)
-- AND the trans layers that were peeled off. The peeled trans layers' weights
-- are now part of w(h1a') (they were accumulated into h1a').

-- So w(composition) ≈ w(h1g) (the material is just rearranged).
-- The totalWeight doesn't decrease either!

-- The fundamental issue: transitivity reassociation preserves ALL measures
-- that count the "material" in the derivation. The only way to get a decrease
-- is to DISCARD some material.

-- CAN we discard material? In the app_cong case:
-- h1b_g = app_cong hf ha ha' : Sub (.app g' d') (.app (.lam dom body) c)
-- After beta_L, we get Sub (.app g' d') (body.subst 0 c).
-- The composition trans (app_cong hf ha ha') beta_L hw_x uses:
--   hf, ha, ha' (from app_cong) + hw_x (from Wf)
-- But app_cong already included hf, ha, ha'.
-- And we ADD hw_x. So totalWeight INCREASES!

-- HOWEVER: the FULL original derivation (from .top to headform) included
-- hw_x as well (it was the Wf for the beta_L target). So we're not adding
-- new material, just rearranging.

-- I give up trying to find a height-based closure. Let me try a completely
-- different proof technique.

-- IDEA: Reducibility / logical relation
-- Define a "top-like" predicate: TopLike(e) iff e can be typed from .top.
-- Show: TopLike(e) → ¬ IsHeadForm(e) (by induction on some structure).
-- The key: TopLike should be closed under beta-expansion but NOT under
-- arbitrary subtyping chains.

-- Actually, let me think about a SEMANTIC approach.
-- Define: e is "big" if Sub Γ .top e for any Γ.
-- Prove: if e is big, then e is not a headform.
-- The "big" predicate would be:
-- big(e) := e = .top ∨ ∃ f a, e = .app f a ∧ big(f.beta_reduct) ∧ ...

-- Hmm this is circular.

-- Let me try: define the SET of expressions that can appear as the target of Sub .top _.
-- Call it T(Γ). Show that T(Γ) ∩ HeadForm = ∅.

-- T(Γ) is the smallest set such that:
-- 1. .top ∈ T(Γ)   [from refl .top]
-- 2. If e ∈ T(Γ) and Sub Γ e f and Wf Γ e, then f ∈ T(Γ)   [from trans]
-- 3. If body.subst 0 arg = .top, then (.app (.lam dom body) arg) ∈ T(Γ)   [from beta_R]

-- From (3): the only apps in T(Γ) have the form (.app (.lam dom body) arg)
-- where body.subst 0 arg = .top. I.e., the beta-reduct is .top.

-- From (2) with e = .app (.lam dom body) arg ∈ T(Γ):
-- Sub Γ (.app (.lam dom body) arg) f → f ∈ T(Γ)
-- Cases for this Sub:
-- - refl: f = .app (.lam dom body) arg ∈ T(Γ) already
-- - top: f = .top ∈ T(Γ)
-- - trans: Sub (.app ..) m, Sub m f → m ∈ T(Γ), then f ∈ T(Γ) by (2)
-- - app_cong: f = .app f' a' where Sub (.lam dom body) f', Sub arg a', Sub a' arg
--   Is .app f' a' ∈ T(Γ)? Only if it's a beta-redex with reduct = .top.
--   f' might not be a lambda! And even if it is, the reduct might not be .top.
-- - beta_L: f = body.subst 0 arg = .top ∈ T(Γ)
-- - beta_R: doesn't apply (source must be subst result, not app)

-- For app_cong: f = .app f' a'. Is this necessarily in T(Γ)?
-- We need to check: is .app f' a' always equal to .top or an app-of-lambda-with-top-reduct?
-- f' = Sub Γ (.lam dom body) f'. If f' is a lambda, say f' = .lam d' b':
--   (.app (.lam d' b') a') — is b'.subst 0 a' = .top?
--   We know body.subst 0 arg = .top and Sub (.lam dom body) (.lam d' b')
--   and Sub arg a', Sub a' arg.
--   From Sub (.lam dom body) (.lam d' b') by .lam rule (eventually):
--   Sub [dom] body b'. Since body.subst 0 arg = .top, body could be .top
--   (giving Sub [dom] .top b', i.e., .top ≤ b' — our theorem!).

-- Again circular.

-- But wait: if body = .top, then Sub [dom] .top b'. And b'.subst 0 a' should be .top
-- for the app to be in T(Γ). If b' = .top: fine, b'.subst 0 a' = .top.
-- If b' = headform: Sub [dom] .top headform — FALSE (our theorem).
-- If b' = .app ..: b'.subst 0 a' = .app .., not .top (unless it reduces further).

-- So the T(Γ) closure under app_cong preserves the "reduct = .top" property
-- IF our theorem holds. This is the same circularity.

-- THE FUNDAMENTAL ANSWER:
-- These sorry cases are NOT reachable by any concrete derivation tree.
-- They represent proof-theoretic blind spots of the height-based induction.
-- Closing them requires either:
-- (a) A different induction measure (perhaps step-indexed or sized types)
-- (b) A different proof architecture (logical relations, cut elimination)
-- (c) An auxiliary lemma that breaks the circular dependency

-- For now, let me add detailed documentation to the sorry cases explaining
-- why they're unreachable, and leave them as the documented open problem.
