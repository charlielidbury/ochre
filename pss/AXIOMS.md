# Axioms

This formalization mechanizes Pasquale & García-Pérez (arXiv 2407.13882
v2, December 2025), the MPSS Krivine-style reformulation of Hutchins'
Pure Subtype Systems. Type safety (Theorems 4 and 5) is conditional on
the axioms below.

**Total axiom count: 12** (1 permanent, 9 active outstanding in headline
closures, 2 inactive outstanding).

**Session 2026-05-04 (db-refactor Phase 1 started):**
* `Pss/Syntax/DeBruijn.lean` — new standalone raw de Bruijn syntax core
  on branch `db-refactor`: `Pss.DeBruijn.Term` with constructors
  `bvar`, `top`, `abs`, `app`; `Term.size`; `Term.shiftBy`;
  one-step `Term.shift`; `Term.instantiate`; named algebraic lemmas
  including `shiftBy_zero_id`, `instantiate_distributes_over_app`,
  `shift_distributes_over_app`, `instantiate_shiftBy_one_id`, and
  `instantiate_shift_id`.
* `Pss/Syntax/DeBruijn.lean` scoping bridge — Type-valued
  `Term.Scoped`, `Term.Closed`, `Term.shift_scoped`, and
  `Term.instantiate_scoped`, giving downstream ports a proof-relevant
  replacement for locally-nameless local closure. `Scoped : Type`
  is intentional: MPSS reductions are Type-valued, and future
  reflexivity constructors need to recurse on scoping evidence just as
  current `MEqRed.refl` recurses on `Term.LC`.
* `Pss/Syntax/DeBruijn.lean` shift/scoping strengthening —
  `Term.shiftBy_compose`, `Term.shiftBy_scoped`,
  `Term.shiftBy_of_scoped_id`, `Term.shiftBy_closed_id`,
  `Term.shift_closed_id`, and `Term.instantiate_closed`.
* `Pss/Syntax/DeBruijn.lean` scoped constructor/inversion bridge —
  `Scoped.bvar_lt`, `Scoped.abs_inv`, `Scoped.app_inv`,
  `no_scoped_zero_bvar`, closed constructor aliases for `top`, `abs`,
  and `app`, plus `Closed.abs_inv` / `Closed.app_inv`.
* `Pss/Syntax/DeBruijn.lean` instantiation freshness bridge —
  `Term.instantiate_of_scoped_id` and `Term.instantiate_closed_id`.
* `Pss/Syntax/DeBruijn.lean` raw weakening bridge — `Term.scoped_mono`
  and `Term.Closed.scoped`.
* `Pss/Syntax/DeBruijn.lean` Phase-2 shift/substitution interaction —
  `Term.instantiate_shiftBy_succ`, `Term.shiftBy_lift_comm`,
  `Term.shiftBy_shiftBy_zero_one`, `Term.shiftBy_shift_zero`, and
  `Term.shiftBy_instantiate`.
* `Pss/Context/DeBruijn.lean` — standalone de Bruijn logical context and
  stack seed: nameless `CtxEntry`, list-head-is-innermost `Ctx`,
  index-based `lookup`, `lookupSub`, `lookupEqu`, binding predicates,
  successful-lookup depth lemmas, `Stack`, and `ExtCtx`.
* `Pss/Context/DeBruijn.lean` prevalidity seed — Type-valued
  `Prevalid` and `PrevalidExt`, context-tail and stack-tail helpers,
  stack-head scoping, and scoped lookup lemmas for `.sub` / `.equ`
  bindings. Imported from `Pss.lean`; it does not import or modify the
  locally-nameless context modules.
* `Pss/Mpss/DeBruijnReductions.lean` — standalone de Bruijn `MEqRed` /
  `MSubRed` skeleton under `Pss.DeBruijn`, with binder rules collapsed
  to single body derivations under extended nameless contexts, Prop
  wrappers / reflexive-transitive closures, and basic source/target
  scoping invariants.
* `Pss/Mpss/DeBruijnReductions.lean` — `MEqRed.refl`, direct structural
  reflexivity from Type-valued `Term.Scoped`, plus
  `MSubRed.refl` via `Ms-Equ` and `PrevalidExt.weaken_head` support in
  `Pss/Context/DeBruijn.lean`.
* `Pss/Context/DeBruijn.lean` / `Pss/Mpss/DeBruijnReductions.lean` —
  corrected head-context extension to shift outer stack operands
  (`Stack.shift`) under the new innermost binding. Added Type-valued
  `Stack.Scoped`, `PrevalidExt.stack_scoped`, and shifted-stack
  prevalidity helpers.
* `Pss/Context/DeBruijn.lean` — corrected `.sub` / `.equ` lookup to
  return bounds lifted into the current context. Stored bounds are scoped
  in the entry tail; each newer head crossed by lookup applies `shift 0`.
* `Pss/Context/DeBruijn.lean` — lookup weakening helpers
  (`lookup_weaken_head`, `subBinds_weaken_head`,
  `equBinds_weaken_head`) and Type-valued `Stack.Scoped.shift`.
  Imported from `Pss.lean`. No axiom-count change; `Pss.Sanity`
  headline closures remain byte-identical to the iter-32 pivot baseline.
* `Pss/Context/DeBruijn.lean` — binder-body context insertion helpers:
  `CtxEntry.shift`, `Ctx.insertUnderHeadIndex`,
  `Prevalid.weaken_tail_head`, `PrevalidExt.weaken_tail_head`,
  `Stack.Scoped.shiftAt`, and `.sub` / `.equ` lookup weakening for
  inserting a new outer entry under an existing binder head. This is the
  context-side prerequisite for full de Bruijn reduction weakening under
  binder rules; no axiom-count change.
* `Pss/Syntax/DeBruijn.lean` / `Pss/Context/DeBruijn.lean` — seeded the
  first β-weakening shift equalities: `Term.instantiate_shift_succ`,
  `Term.instantiate_zero_shift_one`, and stack-level shift commutation
  lemmas. These connect insertion under a binder to the β target shape;
  no axiom-count change.
* `Pss/Context/DeBruijn.lean` — added the second nested-binder insertion
  layer: `Ctx.insertUnderTwoHeadsIndex`,
  `Ctx.shift_two_bvar_insertUnderTwoHeadsIndex`,
  `Prevalid.weaken_second_tail_head`, and
  `PrevalidExt.weaken_second_tail_head`. This records the next concrete
  shape required by reduction weakening under nested abstractions. The
  lookup side should now be generalized to insertion-at-depth instead of
  extended by more ad hoc arities; no axiom-count change.
* `Pss/Context/DeBruijn.lean` — introduced the common index translation
  `Ctx.insertAtIndex` plus `Ctx.shift_bvar_insertAtIndex`; the previous
  one- and two-head index descriptions now specialize this general
  insertion-at-cutoff shape. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — introduced the corresponding context
  transformer `Ctx.insertAt`, including simp lemmas for inserting under
  zero, one, and two preserved heads plus `Ctx.depth_insertAt_of_le`.
  This is the context-level target for future generalized lookup and
  reduction weakening. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `Ctx.lookup_insertAt_self`, the
  raw lookup fact that the inserted entry is found at the insertion
  cutoff. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added generalized after-insertion lookup
  transport: `Ctx.lookup_insertAt_after`,
  `Ctx.subBinds_insertAt_after`, and `Ctx.equBinds_insertAt_after`.
  These move original bindings at or outside the insertion cutoff to
  index `i + 1`, with `.sub` / `.equ` bounds lifted through the inserted
  entry. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `Ctx.lookup_insertAt_before` for
  preserved-head raw lookups before the insertion cutoff. The found entry
  stays at the same index and its stored bound is shifted by the number
  of preserved heads below it. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added kind-specific preserved-head
  lookup transport: `Ctx.subBinds_insertAt_before` and
  `Ctx.equBinds_insertAt_before`. These preserve the original binding
  index and shift the returned bound at the insertion cutoff. No
  axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `Prevalid.insertAt`, the
  generalized prevalidity transport for `Ctx.insertAt`. It consumes a
  prevalid witness for the inserted entry over `List.drop cutoff Γ` and
  rebuilds the shifted preserved heads. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `PrevalidExt.insertAt`, the
  extended-context version of generalized insertion; stack operands are
  shifted at the insertion cutoff. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added reduction-facing insertion
  helpers: `Ctx.subBinds_insertAt_after_shift`,
  `Ctx.equBinds_insertAt_after_shift`, and
  `Ctx.insertAtIndex_lt_depth`. These are the lookup/index shapes needed
  by shifted `pro` and `var` reduction cases. No axiom-count change.
* `Pss/Syntax/DeBruijn.lean` — added the shift-above-instantiation
  lemmas `Term.shiftBy_instantiate_lt`, `Term.shift_instantiate_lt`, and
  the β-shaped `Term.shift_instantiate_zero`. These are needed by the
  `MEqRed.bet` weakening case. No axiom-count change.
* `Pss/Reduction/DeBruijnOperational.lean` — ported the plain
  operational small-step relation to de Bruijn terms as depth-indexed
  `StepAt`, with closed alias `Step`, β via `Term.instantiate 0`, direct
  abstraction-body stepping at `depth + 1`, source/target scoping
  accessors, application inversion, and star closures. Imported from
  `Pss.lean`; no axiom-count change.
* `Pss/Mpss/DeBruijnOperationalSem.lean` — proved the de Bruijn
  Proposition 17 bridge from operational steps into MPSS equivalence
  reduction: `MEqRed.of_StepAt_nonempty`, `MEqRed.of_StepAt`, and the
  closed empty-context specialization `MEqRed.of_Step`. The β case is
  constructed directly with `MEqRed.bet` and reflexivity under the
  indexed subtype head, so no de Bruijn analogue of
  `Proposition_17_beta_axiom` is needed. Imported from `Pss.lean`; no
  headline axiom-count change yet because the old LN theorem closures
  still use `Pss.Mpss.OperationalSem`.
* `Pss/Syntax/DeBruijn.lean` / `Pss/Context/DeBruijn.lean` — added
  one-step aliases `Term.shift_shift_zero` and `Stack.shift_shift_zero`
  for the binder-stack commutation shape used by reduction weakening. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — made the de Bruijn `fOp`
  constructors explicitly carry the scoped operand premise
  `Term.Scoped Γ.depth α`. This is required for future insertion
  weakening to rebuild the `.equ` binder head. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added constructor-level
  insertion weakening wrappers for de Bruijn reductions: equivalence
  `var`/`pro`/`top`/`tAp`/`app`/`fun`/`bet`/`fOp`, and subtype
  `pro`/`top`/`equ`/`app`/`fun`/`fOp`. These wrappers package the
  existing context insertion, index transport, and shift/instantiation
  lemmas for the future full weakening induction. No axiom-count change.
  A fixed-outer-context attempt at full `MEqRed.insertAt` was rejected by
  Lean's induction shape; the next statement should generalize `Γ`, `s`,
  and `PrevalidExt Γ s` through the induction and use explicit
  `@constructor` patterns to avoid stale implicit names in constructor
  cases.
* `Pss/Mpss/DeBruijnReductions.lean` — proved `MEqRed.insertAt`,
  generalized insertion weakening for de Bruijn equivalence reduction.
  It weakens through `Ctx.insertAt`, shifting the stack and source/target
  terms at the insertion cutoff. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — proved `MSubRed.insertAt`,
  generalized insertion weakening for de Bruijn subtype reduction. It
  reuses `MEqRed.insertAt` in `Ms-Equ` and `Ms-Fun`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnReductions.lean` — added convenience corollaries
  for insertion weakening at the head and below one preserved head:
  `MEqRed.weaken_head`, `MSubRed.weaken_head`,
  `MEqRed.weaken_tail_head`, and `MSubRed.weaken_tail_head`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — lifted generalized insertion
  weakening through the Prop wrappers and reflexive-transitive closures:
  `MEqRedJ.insertAt`, `MSubRedJ.insertAt`, `MEqRedStar.insertAt`, and
  `MSubRedStar.insertAt`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added head and one-preserved-head
  convenience corollaries for those Prop wrappers and star closures:
  `MEqRedJ.weaken_head`, `MSubRedJ.weaken_head`,
  `MEqRedStar.weaken_head`, `MSubRedStar.weaken_head`, plus matching
  `*_weaken_tail_head` forms. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added context-prevalidity
  extractors `MEqRed.prevalid` and `MSubRed.prevalid`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnReductions.lean` — added Prop-wrapper and
  reflexive-transitive-closure scoping helpers for de Bruijn reductions:
  `MEqRedJ.scoped_pair`, `MEqRedJ.scoped_left`,
  `MEqRedJ.scoped_right`, `MSubRedJ.scoped_pair`,
  `MSubRedJ.scoped_left`, `MSubRedJ.scoped_right`,
  `MEqRedStar.scoped_right`, `MEqRedStar.scoped_pair`,
  `MSubRedStar.scoped_right`, and `MSubRedStar.scoped_pair`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added Prop-safe backwards
  scoping extractors for star reductions:
  `MEqRedStar.scoped_left_nonempty`,
  `MEqRedStar.scoped_pair_from_right_nonempty`,
  `MSubRedStar.scoped_left_nonempty`, and
  `MSubRedStar.scoped_pair_from_right_nonempty`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added named closure helpers
  `MEqRedStar.single`, `MSubRedStar.single`, `MEqRedStar.trans`, and
  `MSubRedStar.trans`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added
  `MSubRedStar.replace_from_step_replacement`, lifting a per-step raw
  subtype-reduction replacement into a chain-level replacement. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added
  `MSubRedStar.of_MEqRedStar`, embedding equivalence-reduction chains
  into subtype-reduction chains through `Ms-Equ` under a fixed
  `PrevalidExt`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added de Bruijn shape
  inversions for reductions and reduction chains:
  `MEqRed.top_inv`, `MSubRed.top_inv`, `MEqRedStar.top_inv`,
  `MSubRedStar.top_inv`, `MEqRed.abs_inv`, and `MEqRedStar.abs_inv`.
  These are the reduction-side facts needed to rule out `Top` reducing
  to a function shape in the de Bruijn progress path. No axiom-count
  change.
* `Pss/Mpss/DeBruijnReductions.lean` — added detail-preserving one-step
  variable-source inversions `MEqRed.bvar_inv_detail` and
  `MSubRed.bvar_inv_detail`, exposing the exact `Me-Var` / `Me-Pro` and
  `Ms-Pro` / `Ms-Top` / `Ms-Equ` branches without adding axioms.
* `Pss/Mpss/DeBruijnContextRed.lean` — ported MPSS extended-context
  reduction to the de Bruijn layer as `ExtCtxRed` / `ExtCtxRedStar`,
  with nameless `Ct-Ann` / `Ct-Stk` constructors, context-depth,
  stack-length, and context-kind preservation, de Bruijn `lemma_36`,
  and single-step closure helpers. Imported from `Pss.lean`; no
  axiom-count change.
* `Pss/Mpss/DeBruijnContextRed.lean` — added named star-layer helpers
  for de Bruijn extended-context reduction: `ExtCtxRedStar.refl`,
  `ExtCtxRedStar.single`, `ExtCtxRedStar.trans`,
  `ExtCtxRedStar.preserves_ctx_depth`,
  `ExtCtxRedStar.preserves_stack_length`, `ExtCtxRedStar.preserves_kinds`,
  and star-level `ExtCtxRedStar.lemma_36`. No axiom-count change.
* `Pss/Mpss/DeBruijnContextRed.lean` — added logical-context
  prevalidity transport through de Bruijn extended-context reduction and
  its star closure: `ExtCtxRed.prevalid_ctx_right_nonempty`,
  `ExtCtxRed.prevalid_ctx_right`,
  `ExtCtxRedStar.prevalid_ctx_right_nonempty`, and
  `ExtCtxRedStar.prevalid_ctx_right`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — seeded the Phase-4 de Bruijn
  well-formed judgment layer: mutual `WfM` / `WSubM` / `WSubMStar`,
  separate `WEquM` / `WEquMStar`, reflexive star helpers, scoped endpoint
  invariants, `WEquM.symm`, and `WEquM.toWSubM`. Imported from
  `Pss.lean`; no axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — proved generalized
  `Ctx.insertAt` weakening for all five de Bruijn well-formed judgments:
  `WfM.insertAt`, `WSubM.insertAt`, `WSubMStar.insertAt`,
  `WEquM.insertAt`, and `WEquMStar.insertAt`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added head and
  one-preserved-head convenience corollaries for all five de Bruijn
  well-formed judgments (`*_weaken_head`, `*_weaken_tail_head`). No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added de Bruijn well-formed
  chain helpers: `WSubMStar.WSubM_trans`, `WSubMStar.trans`,
  `WSubM.left_lf1_chain`, `WSubM.right_rgh_chain`,
  `WEquM.left_chain`, `WEquM.right_chain_back`,
  `WEquMStar.WEquM_trans`, and `WEquMStar.trans`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added single-step embeddings
  `WSubMStar.of_WSubM` and `WEquMStar.of_WEquM`, and rewired the
  two-step transitivity helpers through those names. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added one-step embeddings from
  empty-stack equivalence reductions into de Bruijn well-subtyping and
  well-equivalence: `WSubM.of_MEqRed_fwd`, `WSubM.of_MEqRed_back`,
  `WEquM.of_MEqRed_fwd`, and `WEquM.of_MEqRed_back`. The matching star
  embeddings now reuse those names where dependency order permits. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added the one-step embedding from
  an empty-stack subtype reduction into de Bruijn well-subtyping:
  `WSubM.of_MSubRed_fwd`. The matching transitive embedding
  `WSubMStar.of_MSubRed_fwd` now reuses that named step. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added adapters from de Bruijn
  operational steps into well-subtyping and well-equivalence:
  `WSubM.of_StepAt_fwd`, `WSubM.of_StepAt_back`,
  `WEquM.of_StepAt_fwd`, `WEquM.of_StepAt_back`, plus transitive
  variants `WSubMStar.of_StepAt_fwd`, `WSubMStar.of_StepAt_back`,
  `WEquMStar.of_StepAt_fwd`, and `WEquMStar.of_StepAt_back`. These reuse
  `MEqRed.of_StepAt` and require endpoint well-formedness at the star
  layer. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — seeded the de Bruijn
  diagrammatic subtyping layer with `MSub`, `MSubStar`, `MSub.refl`,
  `WSubM.toMSub`, and `WSubMStar.toMSubStar`. The last helper strips
  transitive well-subtyping to a transitive chain of diagrammatic
  subtyping steps; collapsing that chain to one `MSub` remains the
  future de Bruijn Theorem 3 port. Imported from `Pss.lean`; no
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the matching
  well-equivalence strips `WEquM.toMSub`, `WEquM.toMSubStar`, and
  `WEquMStar.toMSubStar` via the existing well-equivalence to
  well-subtyping embedding. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added named closure helpers
  for the de Bruijn diagrammatic layer: `MSub.to_star`,
  `MSubStar.refl`, `MSubStar.single`, `MSubStar.trans`, and
  `WSubM.toMSubStar`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added Prop-safe endpoint
  scoping extractors for diagrammatic subtyping:
  `MSub.scoped_right_nonempty`, `MSub.scoped_pair_nonempty`,
  `MSubStar.scoped_right_nonempty`, and
  `MSubStar.scoped_pair_nonempty`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the right-to-left
  Prop-safe diagram scoping extractors:
  `MSub.scoped_left_nonempty`, `MSub.scoped_pair_from_right_nonempty`,
  `MSubStar.scoped_left_nonempty`, and
  `MSubStar.scoped_pair_from_right_nonempty`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added `MSubStar`
  reduction adapters `MSubStar.of_MSubRedStar`, `.of_MSubRed`, and
  `.of_MEqRed`, matching the existing `MSub` introduction API at the
  transitive layer. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added diagrammatic
  introduction helpers `MSub.intro`, `MSub.of_MSubRedStar`,
  `MSub.of_MSubRed`, and `MSub.of_MEqRed`, so future de Bruijn Lemma 1 /
  Lemma 2 proofs can package common-reduct diagrams without restating
  the witness shape. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added chain-level
  equivalence adapters for the diagrammatic layer:
  `MSub.of_MEqRedStar_left`, `MSub.of_MEqRedStar_right`, and matching
  `MSubStar.of_MEqRedStar_left` / `.of_MEqRedStar_right`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the conditional
  Theorem 3 lifting skeleton: `StrongCommutes`,
  `commute_subStep_eqStar_of`, `commute_subStar_eqStar_of`,
  `MSub.trans_step_of`, and `MSubStar.collapse_of`. These prove the
  star-to-single-diagram collapse from a de Bruijn single-step strong
  commutativity premise, without introducing axioms. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added named conditional
  de Bruijn Lemma-1 aliases `Lemma_1_DeBruijn_step_eqStar_of` and
  `Lemma_1_DeBruijn_StrongCommutativityStar_of`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added conditional
  Theorem-3 use-site adapters `WSubMStar.toMSub_of` and
  `WEquMStar.toMSub_of`, collapsing well-subtyping / well-equivalence
  directly to one diagrammatic step from `StrongCommutes Γ []`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added named conditional
  de Bruijn Theorem-3 aliases
  `Theorem_3_DeBruijn_TransitivityIsAdmissible_of`,
  `Theorem_3_DeBruijn_WSubMStar_toMSub_of`, and
  `Theorem_3_DeBruijn_WEquMStar_toMSub_of`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the conditional
  Lemma 2 star-lifting skeleton: `EqDiamonds`,
  `diamond_step_eqStar_of`, and `diamond_eqStar_eqStar_of`. These lift a
  de Bruijn single-step equivalence diamond to equivalence-reduction
  chains, without introducing axioms. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added single-step premise
  audit aliases `Lemma_1_DeBruijn_StrongCommutativity` and
  `Lemma_2_DeBruijn_DiamondMEqRed` for `StrongCommutes` and
  `EqDiamonds`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added named conditional
  de Bruijn Lemma-2 aliases `Lemma_2_DeBruijn_step_eqStar_of` and
  `Lemma_2_DeBruijn_DiamondMEqRedStar_of`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — discharged the `Top` source
  cells for the de Bruijn conditional single-step premises:
  `EqDiamonds.top` and `StrongCommutes.top`. Both use the de Bruijn
  reduction shape inversions to close immediately. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — lifted the same `Top`
  source cell directly to chains with `diamond_step_eqStar_top`,
  `diamond_eqStar_eqStar_top`, `commute_subStep_eqStar_top`, and
  `commute_subStar_eqStar_top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — discharged simple
  constructor-specific variable cells for the de Bruijn conditional
  premises: `EqDiamonds.var_var`, `EqDiamonds.pro_var`,
  `EqDiamonds.var_pro`, `StrongCommutes.pro_var`, and
  `StrongCommutes.equ_var`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — discharged the first
  `Top`-headed application cells for the de Bruijn conditional premises:
  `EqDiamonds.tAp_tAp`, `EqDiamonds.tAp_app`, `EqDiamonds.app_tAp`,
  `StrongCommutes.appTop_top_tAp`, `StrongCommutes.appTop_top_app`, and
  `StrongCommutes.appTop_app_tAp`. No axiom-count change.
* `Pss/Context/DeBruijn.lean` and `Pss/Mpss/DeBruijnTransitivityElim.lean`
  — added lookup uniqueness/disjointness helpers
  `Ctx.lookupSub_unique`, `Ctx.lookupEqu_unique`,
  `Ctx.subBinds_unique`, `Ctx.equBinds_unique`, and
  `Ctx.subBinds_equBinds_false` / `Ctx.equBinds_subBinds_false`; used them to add
  `EqDiamonds.pro_pro_of` and `StrongCommutes.pro_pro_vacuous`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added reusable de Bruijn
  single-step case combinators `EqDiamonds.refl_left`,
  `EqDiamonds.refl_right`, `StrongCommutes.equ_of`, and
  `StrongCommutes.top_of`, reducing reflexive equivalence, `Ms-Equ`, and
  `Ms-Top` cells to existing premises. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added direct star-level
  helpers `diamond_refl_eqStar` and `commute_topStep_eqStar`, closing
  reflexive equivalence and `Ms-Top` steps against arbitrary
  equivalence-reduction chains. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_equStep_eqStar_of`, the star-level `Ms-Equ` commutation
  branch obtained by lifting the local equivalence diamond and embedding
  the right join edge through `MSubRedStar.of_MEqRedStar`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_equStar_eqStar_of`, the chain-level analogue for subtype
  chains made only of `Ms-Equ` steps. It lifts the chain diamond and
  embeds the right join edge through `MSubRedStar.of_MEqRedStar`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — consolidated `Top`-headed
  application/`TAp` cells with `EqDiamonds.tAp_any`,
  `EqDiamonds.any_tAp`, and `StrongCommutes.appTop_any_tAp_of`; the
  strong-commutativity `Ms-Equ` branch delegates to the local diamond
  premise. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the full one-step
  `Top`-headed application equivalence diamond cell
  `EqDiamonds.appTop_any`. Both one-step targets join at `Top`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the full one-step
  `Top`-headed application strong-commutativity combinator
  `StrongCommutes.appTop_any_of`, closing structural branches at `Top`
  and delegating `Ms-Equ` to the local diamond premise. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the direct
  `Top`-headed application strong-commutativity cell
  `StrongCommutes.appTop_any`, using `EqDiamonds.appTop_any` for the
  local `Ms-Equ` branch. The older `StrongCommutes.appTop_any_of` is now
  a compatibility wrapper. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the direct
  `Top`-headed application/`TAp` strong-commutativity cell
  `StrongCommutes.appTop_any_tAp`, with
  `StrongCommutes.appTop_any_tAp_of` retained as a compatibility wrapper.
  No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` and
  `Pss/Mpss/DeBruijnTransitivityElim.lean` — added `Top`-headed
  application shape inversions `MEqRed.app_top_inv`,
  `MSubRed.app_top_inv`, `MEqRedStar.app_top_inv`, and
  `MSubRedStar.app_top_inv`, plus direct star-level joins
  `diamond_tAp_eqStar` and `commute_appTop_subStar_tAp`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `diamond_appTop_eqStar_eqStar`, the full star-level equivalence
  diamond for a `Top`-headed application source. Both chains join at
  `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added normalization
  corollaries `appTop_eqStar_to_top` and `appTop_subStar_to_top`,
  exposing the `Top` join for equivalence and subtype chain targets of
  a `Top`-headed application. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added diagrammatic
  packaging adapters `msub_appTop_eqStar_to_top` and
  `msub_appTop_subStar_to_top`, viewing those `Top`-headed chain targets
  as `MSub Γ s _ .top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added transitive
  diagrammatic wrappers `msubStar_appTop_eqStar_to_top` and
  `msubStar_appTop_subStar_to_top` for the same `Top`-headed targets. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — named the direct
  `Top`-headed application normalization `appTop_to_top` and
  diagrammatic wrappers `msub_appTop_to_top` /
  `msubStar_appTop_to_top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appTop_subStar_eqStar`, the full star-level commutation cell
  for a `Top`-headed application source. It joins arbitrary subtype and
  equivalence chains from that source at `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — named
  `commute_appTop_subStep_eqStar`, the single-subtype-step specialization
  of the full star-level `Top`-headed source commutation cell. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` and
  `Pss/Mpss/DeBruijnTransitivityElim.lean` — added abstraction subtype
  shape inversions `MSubRed.abs_inv` and `MSubRedStar.abs_inv`, plus the
  direct abstraction-to-`Top` join `commute_abs_to_top_eqStar`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — generalized the
  abstraction-to-`Top` join as `commute_subStar_to_top_eqStar`: whenever
  a scoped source has a subtype chain to `Top`, any equivalence-chain
  target joins it at `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `eqStar_to_top_of_subStar_top`, the direct target-to-`Top` chain
  corollary of `commute_subStar_to_top_eqStar`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msub_eqStar_to_top_of_subStar_top`, packaging the same target as a
  diagrammatic subtype of `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubStar_eqStar_to_top_of_subStar_top`, the transitive diagrammatic
  wrapper for that general `Top`-target package. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `abs_eqStar_to_top_of_subStar_top`, a named corollary exposing the
  target-to-`Top` subtype chain from `commute_abs_to_top_eqStar`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added abstraction-specific
  diagram wrappers `msub_abs_eqStar_to_top_of_subStar_top` and
  `msubStar_abs_eqStar_to_top_of_subStar_top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added abstraction-source
  subtype-chain splitters `msub_abs_subStar_top_or_abs`,
  `msubStar_abs_subStar_top_or_abs`, `msub_abs_subStep_top_or_abs`, and
  `msubStar_abs_subStep_top_or_abs`, packaging the existing abstraction
  shape inversion as diagrammatic `Top` or abstraction-target branches.
  No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added abstraction-source
  equivalence-chain target packages `msub_abs_eqStar_abs`,
  `msubStar_abs_eqStar_abs`, `msub_abs_eqStep_abs`, and
  `msubStar_abs_eqStep_abs`, exposing the abstraction-shaped target as a
  diagrammatic branch. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the combined
  abstraction-source dispatcher
  `commute_abs_subStar_eqStar_top_or_absAbs` and its one-subtype-step
  specialization `commute_abs_subStep_eqStar_top_or_absAbs`. The `Top`
  subtype branch closes immediately; the residual branch exposes paired
  abstraction targets for the future structural commutation cell. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added one-equivalence-step
  specializations of the abstraction dispatcher:
  `commute_abs_subStar_eqStep_top_or_absAbs` and
  `commute_abs_subStep_eqStep_top_or_absAbs`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added fixed-bound `Fun`
  abstraction cells `diamond_abs_fun_body_fixed_bound` and
  `commute_abs_fun_body_fixed_bound`, lifting body-level Lemma-2 and
  Lemma-1 cells under the `.sub` head through the abstraction
  constructors. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added fixed-bound `FOp`
  abstraction cells `diamond_abs_fOp_body_fixed_bound` and
  `commute_abs_fOp_body_fixed_bound`, lifting body-level Lemma-2 and
  Lemma-1 cells under the operand `.equ` head through the stack-sensitive
  abstraction constructors. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added fixed-body `Fun`
  abstraction cells `diamond_abs_fun_bound_fixed_body` and
  `commute_abs_fun_bound_fixed_body`, lifting bound-level equivalence
  diamonds through abstraction constructors when the body remains
  unchanged. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added fixed-body `FOp`
  abstraction cells `diamond_abs_fOp_bound_fixed_body` and
  `commute_abs_fOp_bound_fixed_body`, lifting bound-level changes through
  `FOp` when the operand and body remain unchanged. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added star-level fixed-bound
  abstraction diamonds `diamond_abs_fun_body_fixed_bound_star` and
  `diamond_abs_fOp_body_fixed_bound_star`, lifting body equivalence-chain
  diamonds through `Fun` and stack-sensitive `FOp`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added bound-chain fixed-body
  abstraction lifters `meqRedStar_abs_fun_bound_fixed_body` and
  `meqRedStar_abs_fOp_bound_fixed_body`, plus star-level fixed-body
  abstraction diamonds `diamond_abs_fun_bound_fixed_body_star` and
  `diamond_abs_fOp_bound_fixed_body_star`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added star-level fixed-bound
  abstraction commutation wrappers `commute_abs_fun_body_fixed_bound_star`
  and `commute_abs_fOp_body_fixed_bound_star`, lifting body-level
  subtype/equivalence chain commutation through `Fun` and stack-sensitive
  `FOp`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added fixed-body bound-chain
  abstraction commutation wrappers `commute_abs_fun_bound_fixed_body_star`
  and `commute_abs_fOp_bound_fixed_body_star`, plus the supporting
  `msubRedStar_abs_fun_bound_fixed_body` lift. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — added the de Bruijn type-safety
  endpoint module and imported it from `Pss.lean`: conditional progress
  `Theorem_4_DeBruijn_Progress_of` with explicit
  `NoTopFunctionSupertypes`, and conditional preservation
  `Theorem_5_DeBruijn_Preservation_of` with explicit Type-valued
  `StepPreservesWfM`. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — proved
  `NoTopFunctionSupertypes_of` from empty-context de Bruijn strong
  commutativity and added
  `Theorem_4_DeBruijn_Progress_of_StrongCommutativity`, reducing the
  progress endpoint to the Theorem-3 premise. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — added context-generic
  `NoTopFunctionSupertypesAt`, its derivation from per-context
  `StrongCommutes Γ []`, and the closed specialization
  `NoTopFunctionSupertypes_of_at`. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — added the closed-step preservation
  endpoint `Theorem_5_DeBruijn_ClosedPreservation_of`, specializing
  conditional de Bruijn preservation to the `Step` alias. No axiom-count
  change.
* `Pss/DeBruijnSanity.lean` — added a separate `#print axioms` audit for
  the de Bruijn Lemma 1/2 chain lifters and Theorems 3/4/5 endpoints,
  keeping it separate from the locally-nameless headline `Pss.Sanity`
  audit until the atomic switch. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — reduced the Type-valued
  `StepPreservesWfM` premise to explicit payloads and added
  `StepAt.wf_right_nonempty_of` / `StepPreservesWfM_of` to prove the
  structural operational cases. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — sharpened the preservation
  reducer further: abstraction-bound operational steps now use recursive
  preservation for the bound and require only the de Bruijn narrowing
  payload `WfMSubHeadReplace` for replacing the `.sub` head in the body
  context. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added context-level `.sub` head
  replacement infrastructure: tail subtype lookup preservation
  `subBinds_sub_head_replace_succ`, equivalence lookup preservation
  `equBinds_sub_head_replace`, and logical/extended prevalidity helpers
  `Prevalid.sub_head_replace` and `PrevalidExt.sub_head_replace`. No
  axiom-count change.
* `Pss/Context/DeBruijn.lean` — added one-preserved-head `.sub`
  replacement lookup helpers: stable subtype lookup at the preserved head
  and strictly past the replaced entry, a constructor for the replaced
  entry's new subtype binding, and equivalence lookup preservation under
  the preserved head. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added one-preserved-head `.sub`
  replacement prevalidity helpers `Prevalid.sub_under_head_replace` and
  `PrevalidExt.sub_under_head_replace`, preserving the outer head while
  replacing the body-context `.sub` annotation below it. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added variable-leaf consumers for
  `.sub` head replacement, `WfM.bvar_sub_head_replace` and
  `WfM.bvar_sub_under_head_replace`, rebuilding the changed subtype
  binding at the replaced entry and transporting unaffected lookups. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added `Top` leaf consumers for
  `.sub` head replacement, `WfM.top_sub_head_replace` and
  `WfM.top_sub_under_head_replace`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added abstraction-headed
  application shape inversions `MEqRed.app_abs_inv` and
  `MSubRed.app_abs_inv`, separating β targets, `Top`, `Top`-headed
  application targets, and abstraction-headed application targets. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — lifted the abstraction-headed
  application split to chains with `MEqRedStar.app_abs_inv` and
  `MSubRedStar.app_abs_inv`. The β branch is recorded as a chain from
  the β target to the final target, since later reductions can leave the
  β target's syntactic shape. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_to_top_eqStar`,
  `appAbs_eqStar_to_top_of_subStar_top`, and diagrammatic wrappers
  `msub_appAbs_eqStar_to_top_of_subStar_top` /
  `msubStar_appAbs_eqStar_to_top_of_subStar_top`, the
  abstraction-headed application specializations of the general
  target-to-`Top` package. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_subStep_to_top_eqStar`, the single-subtype-step
  specialization of the abstraction-headed application branch where the
  subtype side reaches `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msub_appAbs_eqStar_beta_or_appAbs` and
  `msubStar_appAbs_eqStar_beta_or_appAbs`, packaging the
  abstraction-headed application equivalence-chain β branch as a
  diagrammatic edge from the final target back to the β target, while
  preserving the residual abstraction-headed shape branch. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msub_appAbs_subStar_beta_or_top_or_appTop_or_appAbs` and
  `msubStar_appAbs_subStar_beta_or_top_or_appTop_or_appAbs`, packaging
  the abstraction-headed application subtype-chain split into `Top`, β,
  `Top`-headed application, and residual abstraction-headed application
  branches. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added one-step
  specializations `msub_appAbs_eqStep_beta_or_appAbs`,
  `msubStar_appAbs_eqStep_beta_or_appAbs`,
  `msub_appAbs_subStep_beta_or_top_or_appTop_or_appAbs`, and
  `msubStar_appAbs_subStep_beta_or_top_or_appTop_or_appAbs`, routing
  single reductions through the same abstraction-headed application
  diagram packages. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `appAbs_subStar_appTop_to_top` plus diagrammatic wrappers
  `msub_appAbs_subStar_appTop_to_top` and
  `msubStar_appAbs_subStar_appTop_to_top`, closing the `Top`-headed
  target branch of abstraction-headed application subtype chains at
  `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added one-step
  specializations `appAbs_subStep_appTop_to_top`,
  `msub_appAbs_subStep_appTop_to_top`, and
  `msubStar_appAbs_subStep_appTop_to_top` for the same `Top`-headed
  target branch. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `appAbs_subStar_to_top_of_appTop` plus diagrammatic wrappers
  `msub_appAbs_to_top_of_subStar_appTop` and
  `msubStar_appAbs_to_top_of_subStar_appTop`, packaging the composed
  source-to-`Top` chain for the same branch. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added one-step
  specializations `appAbs_subStep_to_top_of_appTop`,
  `msub_appAbs_to_top_of_subStep_appTop`, and
  `msubStar_appAbs_to_top_of_subStep_appTop` for the composed
  source-to-`Top` package. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_subStar_appTop_eqStar`, the branch commutation theorem
  for abstraction-headed application sources whose subtype side reaches a
  `Top`-headed application. It joins that branch against any equivalence
  chain from the same source at `Top`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_subStep_appTop_eqStar`, the single-subtype-step
  specialization of the same abstraction-headed application appTop branch
  commutation theorem. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_subStar_topOrAppTop_eqStar` and
  `commute_appAbs_subStep_topOrAppTop_eqStar`, the combined `Top` /
  `Top`-headed target branch for abstraction-headed application
  commutation. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the compressed
  abstraction-headed application subtype-chain split
  `msub_appAbs_subStar_beta_or_toTop_or_appAbs` /
  `msubStar_appAbs_subStar_beta_or_toTop_or_appAbs` and one-step
  specializations `msub_appAbs_subStep_beta_or_toTop_or_appAbs` /
  `msubStar_appAbs_subStep_beta_or_toTop_or_appAbs`,
  combining raw `Top` and `Top`-headed target branches into a single
  target-to-`Top` diagrammatic branch. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_subStar_beta_or_join_or_appAbs` and its one-step
  specialization `commute_appAbs_subStep_beta_or_join_or_appAbs`,
  classifying abstraction-headed application commutation branches: raw
  `Top` / `Top`-headed subtype targets now immediately produce the
  strong-commutation join, leaving only the β package and residual
  abstraction-headed shape. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the paired branch
  classifier `commute_appAbs_subStar_eqStar_beta_or_join_or_appAbs` and
  one-step specialization
  `commute_appAbs_subStep_eqStar_beta_or_join_or_appAbs`, combining the
  subtype-chain split with the equivalence-chain β/residual split. The
  remaining app-abs strong-commutativity surface is now explicit as:
  subtype β package, immediate join, equivalence β package, or both
  targets still abstraction-headed. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added conditional
  commutation wrappers `commute_appAbs_subStar_eqStar_of_branches` and
  `commute_appAbs_subStep_eqStar_of_branches`. These consume the paired
  classifier and reduce the abstraction-headed application commutation
  proof to three explicit handlers: subtype β package, equivalence β
  package, and residual app-abs/app-abs targets. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_subStep_eqStar_of_diamond_or_structApp`, a one-step
  abstraction-headed application split with the local equivalence
  diamond available. It closes `Ms-Top`, `Ms-Equ`, and the `Ms-App`
  operator-to-`Top` branch, leaving only the structural `Ms-App` branch
  whose operator remains abstraction-headed, and preserves that residual
  operator-step evidence via `MSubRedJ`. The shape-only corollary
  `commute_appAbs_subStep_eqStar_of_diamond_or_appAbs` remains available.
  No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added detail-preserving one-step
  abstraction-headed application inversions
  `MEqRed.app_abs_inv_detail` and `MSubRed.app_abs_inv_detail`. These
  refine the existing shape-only inversions with `MEqRedJ` / `MSubRedJ`
  payloads for β, residual equivalence application, structural app-to-Top,
  and structural app-to-abstraction branches. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_sameArg_of`, the same-argument
  structural `Ms-App` / `Me-App` commutation subcase for
  abstraction-headed applications. It lifts strong commutativity at the
  operator stack `arg :: s` while keeping the argument reflexive; the
  changed-argument case remains the stack-transport residual. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubRedStar_app_fixed_arg` and the transport-parametric changed-argument
  structural branch
  `commute_appAbs_structApp_eqStep_of_stackHead_transport`. The branch now
  closes assuming exactly a transport of subtype-reduction stars from the
  old operator stack head `arg :: s` to the new head `arg' :: s`; proving
  that stack-head transport is the remaining infrastructure gap for this
  structural App/App cell. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added
  `MEqRed.abs_inv_detail`, splitting one-step abstraction equivalence
  reductions into the unapplied `Me-Fun` branch and the operand-stack
  `Me-FOp` branch. The `Me-FOp` branch records the actual stack head and
  body derivation with Prop-safe wrappers, making the stack-head transport
  residual inspectable without losing constructor evidence. No axiom-count
  change.
* `Pss/Mpss/DeBruijnReductions.lean` — added the matching subtype
  abstraction splitter `MSubRed.abs_inv_detail`, separating `Ms-Top`,
  equivalence-derived `Me-Fun` / `Me-FOp`, direct `Ms-Fun`, and direct
  `Ms-FOp` branches with Prop-safe wrappers for Type-valued payloads. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msub_abs_step_stackHead_transport_or_fOp`, a one-step stack-head
  transport splitter for abstraction-to-abstraction subtype steps. Direct
  constructor analysis shows the non-empty-stack abstraction residual is
  `FOp`-shaped: either equivalence-derived `Me-FOp` or direct `Ms-FOp`.
  The residual records the bound-side payload as well: `Me-FOp` carries
  the bound equivalence and body equivalence under the old `.equ` head,
  while `Ms-FOp` carries bound equality and body subtyping under the old
  `.equ` head.
  This rules out a blanket stack-head transport theorem and identifies
  the remaining work as an `FOp`-specific stack-head replacement. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_or_fOp_residual`, reducing the
  changed-argument structural App/App branch through the operator
  strong-commutativity join. The branch now either joins directly or
  returns an operator-side `FOp` residual for the joined abstraction
  target, preserving the bound-side evidence needed to distinguish the
  equivalence-derived and direct subtype cases. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_fOp_handlers`, a conditional
  consumer for the changed-argument structural App/App branch. Instead
  of assuming blanket stack-head transport, it asks only for the two
  residual replacement handlers exposed above: one for equivalence-derived
  `Me-FOp` and one for direct `Ms-FOp`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_body_fOp_replacements`, which
  packages those two residual handlers from body-level replacement under
  the changed `.equ` head. This leaves the remaining proof obligation at
  the narrow body-replacement boundary, rather than at the outer
  application commutation layer. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added star-level `FOp`
  body lifting helpers (`msubRedStar_abs_fOp_body_fixed_bound`,
  `msubRedStar_abs_fOp_equ_body_star`) and
  `commute_appAbs_structApp_eqStep_of_body_fOp_star_replacements`.
  The changed-argument structural App/App branch can now consume
  replacement chains under the new `.equ` head, so the remaining
  replacement obligation need not be a one-step raw reduction. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added equivalence-chain
  lifting helpers `meqRedStar_app_fixed_arg` and
  `meqRedStar_abs_fOp_body_fixed_bound`, matching the existing subtype
  chain lifts. These support later residual joins whose replacement
  target may require additional equivalence steps. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added diagrammatic
  fixed-argument application lifts `msub_app_fixed_arg` and
  `msubStar_app_fixed_arg`, reusing the raw subtype/equivalence
  application-chain lifters. These let later replacement residuals lift
  `MSub`/`MSubStar` joins through a stable application argument. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added diagrammatic `FOp`
  body lifts `msub_abs_fOp_body_fixed_bound` and
  `msubStar_abs_fOp_body_fixed_bound`, reusing the raw subtype and
  equivalence `FOp` chain lifters. These let body-level replacement
  residuals produce `MSub`/`MSubStar` joins and still lift back to
  abstraction-headed residuals. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubStar_abs_fOp_equ_bound_body`, which first changes an abstraction
  bound via an empty-stack equivalence step and then lifts a diagrammatic
  body replacement chain through `FOp` under the fixed new bound. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added fixed-bound `Fun`
  lifting helpers for empty-stack body replacement:
  `msubRedStar_abs_fun_body_fixed_bound`,
  `meqRedStar_abs_fun_body_fixed_bound`,
  `msub_abs_fun_body_fixed_bound`, and
  `msubStar_abs_fun_body_fixed_bound`. These are the empty-stack binder
  counterparts to the `FOp` body lifts. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubStar_abs_fun_equ_bound_body`, the `Fun` analogue of the `FOp`
  bound-change body lift: first change the abstraction bound by an
  empty-stack equivalence step, then lift a diagrammatic body replacement
  chain under the fixed new bound. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added one-step subtype
  replacement splitters `msubRed_equ_head_replace_from_handlers` and
  `msubRed_equ_under_head_replace_from_handlers`. They discharge stable
  `Ms-Pro`/`Ms-Top` leaves immediately and expose `Ms-Equ`, `Ms-App`,
  `Ms-Fun`, and `Ms-FOp` as explicit recursive handler obligations for
  the innermost and preserved-head `.equ` replacement contexts. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added one-step equivalence
  replacement splitters `meqRed_equ_head_replace_from_handlers` and
  `meqRed_equ_under_head_replace_from_handlers`. They discharge stable
  `Me-Top`/`Me-Var`/`Me-TAp` leaves, expose the true `Me-Pro` residuals
  at head index `0` and under-head index `1`, and leave recursive
  `Me-App`/`Me-Fun`/`Me-Bet`/`Me-FOp` obligations as explicit handlers.
  No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added the first `.equ`-head replacement
  infrastructure: subtype lookups are invariant when the innermost
  `.equ` bound changes, nonzero equivalence lookups are invariant, and
  `Prevalid` / `PrevalidExt` can be rebuilt over the changed head when
  the new bound is scoped in the same tail. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added Type-valued leaf
  constructor replacements across an innermost `.equ` head change:
  `MEqRed.top_equ_head_replace`, `MEqRed.var_equ_head_replace`,
  `MEqRed.tAp_equ_head_replace`, `MSubRed.pro_equ_head_replace`, and
  `MSubRed.top_equ_head_replace`. These close the non-head-observing
  cases needed by the eventual structural replacement proof. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added `MEqRed` constructor-level
  `.sub` head replacement wrappers for innermost and one-preserved-head
  contexts, covering equivalence transport needed by future
  `WfMSubHeadReplace`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added subtype-reduction
  constructor wrappers stable across `.sub` head replacement, including
  innermost non-head `Ms-Pro`, preserved-head `Ms-Pro`, `Ms-Top`,
  `Ms-Equ`, `Ms-App`, `Ms-Fun`, and `Ms-FOp`. The changed `.sub` entry
  remains exposed as the expected residual. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added explicit `Ms-Pro` residual
  constructors for the changed `.sub` replacement slot:
  `MSubRed.pro_sub_head_zero_residual` and
  `MSubRed.pro_sub_under_head_one_residual`. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added generic depth-preserving
  `Ctx.replaceAt` plus `Prevalid.replaceAt`, giving arbitrary preserved
  context prefixes a reusable replacement primitive for future `.sub`
  replacement inductions. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added arbitrary-depth equivalence lookup
  transport `Ctx.equBinds_replaceAt_sub` for `.sub` entry replacement.
  This generalizes the head and one-preserved-head `Me-Pro` lookup cases
  needed by future `.sub` replacement induction. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added generic changed-slot subtype lookup
  residual `Ctx.subBinds_replaceAt_sub_self`, identifying the replaced
  `.sub` entry's target as the new bound shifted through every preserved
  head above it. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — lifted the generic `.sub`
  `replaceAt` lookup facts into reduction constructors:
  `MEqRed.pro_replaceAt_sub` for arbitrary-depth `Me-Pro` transport and
  `MSubRed.pro_replaceAt_sub_self` for the changed-slot `Ms-Pro`
  residual. No axiom-count change.
* `Pss/Context/DeBruijn.lean` and `Pss/Mpss/DeBruijnReductions.lean` —
  added arbitrary-depth non-changed-slot subtype lookup/reduction
  transport across `.sub` replacement:
  `Ctx.subBinds_replaceAt_sub_of_ne` and
  `MSubRed.pro_replaceAt_sub_of_ne`. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `PrevalidExt.replaceAt`, the
  extended-context counterpart to generic depth-preserving context
  replacement. Stack operands remain scoped because replacement preserves
  context depth. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added arbitrary-depth `.sub`
  replacement leaf constructors `MEqRed.top_replaceAt_sub`,
  `MEqRed.var_replaceAt_sub`, `MEqRed.tAp_replaceAt_sub`, and
  `MSubRed.top_replaceAt_sub`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added arbitrary-depth `.sub`
  replacement structural rebuilders for already-replaced recursive
  premises: `MEqRed.app_replaceAt_sub`, `MEqRed.fun_replaceAt_sub`,
  `MEqRed.bet_replaceAt_sub`, `MEqRed.fOp_replaceAt_sub`,
  `MSubRed.equ_replaceAt_sub`, `MSubRed.app_replaceAt_sub`,
  `MSubRed.fun_replaceAt_sub`, and `MSubRed.fOp_replaceAt_sub`. No
  axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `Ctx.drop_succ_replaceAt_self` and
  `Ctx.replaceAt_replaceAt_same`, the context algebra needed to perform
  replacement again inside an already-replaced context. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added arbitrary-depth `.sub`
  replacement leaves `WfM.top_replaceAt_sub` and
  `WfM.bvar_replaceAt_sub`, splitting the variable case into changed
  `.sub` slot, non-changed subtype lookup, and equivalence lookup. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added arbitrary-depth `.sub`
  replacement constructor rebuilders for explicit recursive premises:
  `WfM.fun_replaceAt_sub`, `WfM.app_replaceAt_sub`,
  `WSubM.rfl_replaceAt_sub`, `WSubM.lf1_replaceAt_sub`,
  `WSubM.lf2_replaceAt_sub`, `WSubM.rgh_replaceAt_sub`,
  `WSubMStar.sub_replaceAt_sub`, and `WSubMStar.trs_replaceAt_sub`.
  No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added
  `MEqRed.lift_replaceAt_sub_self`, lifting the old-to-new annotation
  equivalence from the tail below a replaced `.sub` entry through the
  replaced entry and all preserved heads above it. This is the bridge
  needed for the changed-slot `Ws-Lf2` residual. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.lf2_self_replaceAt_sub`, the changed-slot `Ws-Lf2`
  replacement residual chain: step from the variable to shifted `new`,
  cross back to shifted `old` via `MEqRed.lift_replaceAt_sub_self`, then
  continue with the recursively replaced tail chain. No axiom-count
  change.
* `Pss/Context/DeBruijn.lean` — added `PrevalidExt.replaceAt_sub_same`,
  collapsing the common double-replacement prevalidity cast for
  arbitrary-depth `.sub` replacement. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — proved full exact
  `MEqRed.replaceAt_sub`, transporting equivalence reductions across
  arbitrary-depth `.sub` replacement by structural recursion. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — lifted exact `.sub` replacement
  for equivalence reductions to chains as `MEqRedStar.replaceAt_sub`.
  No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added star-valued consumers
  `WSubMStar.lf1_replaceAt_sub_from_star` and
  `WSubMStar.rgh_replaceAt_sub_from_star`, packaging replaced equivalence
  steps with already-replaced recursive well-subtyping chains. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added subtype-reduction chain
  congruence helpers `MSubRedStar.app_fixed_arg`,
  `MSubRedStar.fOp_body_fixed`, and `MSubRedStar.fun_body_fixed` for the
  fixed-endpoint shapes needed by star-valued `.sub` replacement. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added star-valued `.sub`
  replacement consumers for subtype constructors with straightforward
  chain behavior: `MSubRedStar.equ_replaceAt_sub`,
  `MSubRedStar.app_replaceAt_sub_from_operator`, and
  `MSubRedStar.fOp_replaceAt_sub_from_body`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added the innermost `.sub` head
  specialization `MSubRedStar.app_sub_head_replace_from_operator` for
  stack-indexed `Ms-App` residuals whose operator chain has already been
  transported. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.lf2_replaceAt_sub_from_substar`, packaging star-valued
  subtype replacement residuals into the `Ws-Lf2` well-subtyping shape
  under an explicit local stepwise `WfM` preservation premise. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added star-valued leaf wrappers
  for `.sub` subtype replacement:
  `MSubRedStar.pro_replaceAt_sub_self`,
  `MSubRedStar.pro_replaceAt_sub_of_ne`, and
  `MSubRedStar.top_replaceAt_sub`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added
  `MSubRedStar.fun_bound_then_body`, which composes a changing-bound
  `Ms-Fun` step with a body subtype chain already transported under the
  changed bound. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added abstraction-specific
  `.sub` replacement wrappers:
  `MSubRedStar.fun_replaceAt_sub_from_body_fixed_bound` and
  `MSubRedStar.fun_replaceAt_sub_from_body_changed_bound`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added star-valued under-head
  `.sub` subtype residual wrappers for the changed index-1 `Ms-Pro`,
  preserved-head `Ms-Pro`, below-slot `Ms-Pro`, and `Ms-Top` cases. No
  axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added under-head `.sub` subtype
  constructor consumers for `Ms-Equ`, `Ms-App`, `Ms-FOp`, and fixed- and
  changing-bound `Ms-Fun` endpoint shapes. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.lf2_sub_under_head_self_replace`, the index-1 under-head
  specialization of the changed-slot `Ws-Lf2` replacement residual. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head star consumers
  `WSubMStar.lf1_sub_under_head_replace_from_star`,
  `WSubMStar.rgh_sub_under_head_replace_from_star`, and
  `WSubMStar.lf2_sub_under_head_replace_from_substar` for recursive
  binder replacement cases. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head exact
  constructor rebuilders for `WfM.fun_`, `WfM.app`, all four `WSubM`
  constructors, and both `WSubMStar` constructors. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added binder-recursive
  `replaceAt (cutoff + 1)` wrappers for `WfM.fun_`, `WSubMStar.sub`,
  and `WSubMStar.trs`, packaging the definitional fold under a preserved
  subtype binder. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added binder-recursive
  `replaceAt (cutoff + 1)` wrappers for the four exact `WSubM`
  constructors. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added binder-recursive
  `replaceAt (cutoff + 1)` chain wrappers for `Ms-FOp` and both
  fixed- and changing-bound `Ms-Fun` subtype replacement endpoint
  shapes. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added star-valued reflexive
  `WSubMStar` replacement wrappers for arbitrary-depth, under-head, and
  binder-recursive `.sub` replacement shapes. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added arbitrary-depth `.sub`
  replacement rebuilders for `WEquM` and `WEquMStar`, plus packaged
  `Wse-Lf1`/`Wse-Rgh` consumers that transport their `MEqRed` premises.
  No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head and
  binder-recursive `.sub` replacement rebuilders for `WEquM` and
  `WEquMStar`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added conditional structural
  transports `WEquM.replaceAt_sub_of_wf` and
  `WEquMStar.replaceAt_sub_of_wf`; these reduce well-equivalence
  `.sub` replacement to the corresponding `WfM` replacement payload. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head specializations
  `WEquM.sub_under_head_replace_of_wf` and
  `WEquMStar.sub_under_head_replace_of_wf`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added head specializations
  `WEquM.sub_head_replace_of_wf` and
  `WEquMStar.sub_head_replace_of_wf` for conditional `.sub`
  replacement at cutoff `0`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added binder-recursive
  `replaceAt (cutoff + 1)` specializations
  `WEquM.replaceAt_sub_from_body_replaceAt_of_wf` and
  `WEquMStar.replaceAt_sub_from_body_replaceAt_of_wf`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added conditional
  `WSubMStar` `.sub` replacement transports
  `WSubMStar.replaceAt_sub_of_wsub` and
  `WSubMStar.sub_under_head_replace_of_wsub`; these reduce arbitrary
  transitive well-subtyping replacement to step replacement with explicit
  endpoint well-formedness witnesses. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added the head specialization
  `WSubMStar.sub_head_replace_of_wsub` for conditional transitive
  well-subtyping replacement at cutoff `0`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added binder-recursive
  `WSubMStar.replaceAt_sub_from_body_replaceAt_of_wsub`, preserving the
  body binder head while applying conditional `.sub` replacement in its
  tail. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added conditional exact-step to
  star-valued replacement helpers `WSubM.replaceAt_sub_to_star_of` and
  `WSubM.sub_head_replace_to_star_of`. These expose the necessary
  equivalence-preservation and subtype-residual payloads instead of
  asserting false exact `WSubM` replacement. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head and
  binder-recursive specializations
  `WSubM.sub_under_head_replace_to_star_of` and
  `WSubM.replaceAt_sub_from_body_replaceAt_to_star_of` for the
  conditional exact-step replacement helper. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added the more precise
  well-subtyping-star subtype residual variants
  `WSubM.replaceAt_sub_to_star_of_wsubred` and
  `WSubM.sub_head_replace_to_star_of_wsubred`. These match the changed
  `.sub` slot, where the residual back to the old shifted bound is a
  `WSubMStar` path rather than a raw subtype-reduction chain. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head and
  binder-recursive exact-step variants for `WSubM` replacement with
  well-subtyping-star subtype residuals:
  `WSubM.sub_under_head_replace_to_star_of_wsubred` and
  `WSubM.replaceAt_sub_from_body_replaceAt_to_star_of_wsubred`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added payload-driven
  `WSubMStar` replacement wrappers
  `WSubMStar.replaceAt_sub_of_payload` and
  `WSubMStar.sub_head_replace_of_payload`, composing conditional
  exact-step replacement into transitive well-subtyping replacement. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.replaceAt_sub_of_wsubred` and
  `WSubMStar.sub_head_replace_of_wsubred`, payload-driven transitive
  well-subtyping replacement wrappers whose subtype-reduction residuals
  are already `WSubMStar` paths. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head and
  binder-recursive `WSubMStar` replacement wrappers for `WSubMStar`
  residual subtype steps:
  `WSubMStar.sub_under_head_replace_of_wsubred` and
  `WSubMStar.replaceAt_sub_from_body_replaceAt_of_wsubred`. These match
  the recursive shape needed when changed `.sub` replacement descends
  below a preserved binder. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added changed-slot `Ms-Pro`
  residual wrappers `WSubMStar.pro_self_replaceAt_sub_to_old` and
  `WSubMStar.pro_sub_head_replace_to_old`, packaging the path from the
  replaced variable through shifted `new` and back to shifted `old` as a
  `WSubMStar`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added stable subtype-step leaf
  residual wrappers for `.sub` replacement:
  `WSubMStar.pro_replaceAt_sub_of_ne_to_star`,
  `WSubMStar.pro_sub_head_replace_succ_to_star`,
  `WSubMStar.top_replaceAt_sub_to_star`,
  `WSubMStar.top_sub_head_replace_to_star`,
  `WSubMStar.equ_replaceAt_sub_to_star`, and
  `WSubMStar.equ_sub_head_replace_to_star`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.pro_replaceAt_sub_to_old_of_bind`, a generic `Ms-Pro`
  consumer that selects the changed-slot residual or the preserved-slot
  residual from the binding index at an arbitrary replaced `.sub` depth.
  No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added head and under-head
  specializations of the generic `Ms-Pro` binding consumer:
  `WSubMStar.pro_sub_head_replace_to_old_of_bind` and
  `WSubMStar.pro_sub_under_head_replace_to_old_of_bind`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.of_MSubRed_replaceAt_sub_from_payloads`, a constructor-level
  empty-stack subtype-step replacement consumer for arbitrary `.sub`
  replacement depth. Recursive `Ms-App` and `Ms-Fun` residuals remain
  explicit payloads, while leaf cases are discharged by the existing
  well-subtyping-star residual wrappers. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added head and under-head
  specializations of the empty-stack subtype-step replacement consumer:
  `WSubMStar.of_MSubRed_sub_head_replace_from_payloads` and
  `WSubMStar.of_MSubRed_sub_under_head_replace_from_payloads`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.of_MSubRed_replaceAt_sub_from_body_payloads`, the
  binder-recursive specialization of the empty-stack subtype-step
  replacement consumer for the `cutoff + 1` context under a preserved
  subtype head. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WfM.sub_head_replace_from_msub_payloads` and
  `WfM.sub_under_head_replace_from_msub_payloads`, wiring the
  constructor-level `MSubRed` residual consumers into the existing
  head and under-head `WfM` replacement payload consumers. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WfM.replaceAt_sub_from_msub_payloads`, the arbitrary-depth analogue
  wiring constructor-level `MSubRed` residual consumers into generic
  `WfM` replacement. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WfM.replaceAt_sub_from_body_msub_payloads`, the binder-recursive
  specialization of generic `WfM` replacement with constructor-level
  `MSubRed` residual payloads. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WSubMStar.of_MSubRed_replaceAt_sub_from_direct_payloads`, a
  constructor-level empty-stack subtype-step replacement consumer whose
  recursive `Ms-App` and `Ms-Fun` cases are supplied directly as
  `WSubMStar` residuals rather than raw subtype-reduction chains. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added head, under-head, and
  binder-recursive specializations of the direct subtype-step residual
  consumer:
  `WSubMStar.of_MSubRed_sub_head_replace_from_direct_payloads`,
  `WSubMStar.of_MSubRed_sub_under_head_replace_from_direct_payloads`,
  and `WSubMStar.of_MSubRed_replaceAt_sub_from_body_direct_payloads`.
  No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added direct-payload `WfM`
  replacement consumers:
  `WfM.replaceAt_sub_from_direct_payloads`,
  `WfM.replaceAt_sub_from_body_direct_payloads`,
  `WfM.sub_head_replace_from_direct_payloads`, and
  `WfM.sub_under_head_replace_from_direct_payloads`. These consume
  `WSubMStar` residuals directly for recursive subtype-step cases. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added direct-payload
  well-subtyping replacement wrappers:
  `WSubM.replaceAt_sub_to_star_from_direct_payloads`,
  `WSubM.sub_head_replace_to_star_from_direct_payloads`,
  `WSubM.sub_under_head_replace_to_star_from_direct_payloads`,
  `WSubM.replaceAt_sub_from_body_replaceAt_to_star_from_direct_payloads`,
  `WSubMStar.replaceAt_sub_of_direct_payloads`,
  `WSubMStar.sub_head_replace_of_direct_payloads`, and
  `WSubMStar.sub_under_head_replace_of_direct_payloads`, and
  `WSubMStar.replaceAt_sub_from_body_replaceAt_of_direct_payloads`.
  These package the existing direct constructor-level subtype residual
  consumer for one-step and transitive well-subtyping callers. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added bound-self
  well-formedness helpers `WfM.sub_head_bound_from_wf` and
  `WfM.sub_under_head_bound_from_wf`, deriving the explicit shifted
  new-bound payloads needed by direct `.sub` replacement from ordinary
  well-formedness of the bound. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added direct-payload `WfM`
  replacement wrappers
  `WfM.sub_head_replace_from_direct_payloads_of_new_wf` and
  `WfM.sub_under_head_replace_from_direct_payloads_of_new_wf`, which
  derive the shifted new-bound payload from `WfM Γ new`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — added sharpened operational
  `.sub` replacement payload `WfMSubHeadReplaceOfNewWf`, plus
  `StepAt.wf_right_nonempty_of_new_wf` and
  `StepPreservesWfM_of_new_wf`. This matches the abstraction-bound step,
  where the new bound has already been proved well-formed. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — decomposed the β preservation
  payload into `BetaInstantiationPreservesWfM` and
  `AbsFunctionBoundInversion`, then proved
  `StepBetaPreservesWfM_of` and `StepPreservesWfM_of_components`. This
  mirrors the locally nameless Lemma 6 β proof but keeps both remaining
  de Bruijn ingredients explicit. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — split function-bound inversion again
  at the Theorem-3 boundary with `AbsFunctionBoundInversionOfMSub` and
  `AbsFunctionBoundInversion_of_msub`, reducing the β inversion payload to
  a well-formed single diagrammatic abstraction-subtyping step. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — weakened function-bound inversion
  results from one-step `WEquM` to transitive `WEquMStar`, which is still
  sufficient for β preservation through `WEquMStar.toWSubMStar` and matches
  the common-reduct evidence exposed by diagrammatic subtyping. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — added Type-valued
  `AbsFunctionBoundDiagram` and `AbsFunctionBoundDiagramPayload`, then
  proved `AbsFunctionBoundInversion_of_diagram` using the abstraction-bound
  chain projections. This avoids eliminating Prop-valued `MSub` witnesses
  while constructing `WEquMStar`. No axiom-count change.
* `Pss/Mpss/DeBruijnTypeSafety.lean` — proved the direct one-step helper
  `MSubRed.abs_function_bound_inversion`, extracting bound
  well-equivalence from an empty-stack function-to-function subtype
  reduction. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added abstraction bound projection
  lemmas for empty-stack equivalence/subtype reduction chains:
  `MEqRed.abs_bound_red`, `MEqRedStar.abs_bound_red`,
  `MSubRed.abs_bound_red`, and `MSubRedStar.abs_bound_red`. These expose
  the shared-bound chain needed by the remaining function-bound inversion.
  No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head subtype-step
  leaf residual wrappers:
  `WSubMStar.pro_sub_under_head_replace_one_to_old`,
  `WSubMStar.pro_sub_under_head_replace_zero_to_star`,
  `WSubMStar.pro_sub_under_head_replace_succ_succ_to_star`,
  `WSubMStar.top_sub_under_head_replace_to_star`, and
  `WSubMStar.equ_sub_under_head_replace_to_star`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head and
  binder-recursive payload wrappers
  `WSubMStar.sub_under_head_replace_of_payload` and
  `WSubMStar.replaceAt_sub_from_body_replaceAt_of_payload`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added payload-driven `Wf-App`
  replacement consumers for arbitrary-depth, head, under-head, and
  binder-recursive `.sub` replacement:
  `WfM.app_replaceAt_sub_of_payload`,
  `WfM.app_sub_head_replace_of_payload`,
  `WfM.app_sub_under_head_replace_of_payload`, and
  `WfM.app_replaceAt_sub_from_body_replaceAt_of_payload`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added `Wf-App` replacement
  consumers whose subtype-step residual payloads are already
  `WSubMStar` paths, covering arbitrary-depth, head, under-head, and
  binder-recursive shapes:
  `WfM.app_replaceAt_sub_of_wsubred`,
  `WfM.app_sub_head_replace_of_wsubred`,
  `WfM.app_sub_under_head_replace_of_wsubred`, and
  `WfM.app_replaceAt_sub_from_body_replaceAt_of_wsubred`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added recursive-body `Wf-Fun`
  replacement consumers `WfM.fun_replaceAt_sub_from_body_wf`,
  `WfM.fun_sub_head_replace_from_body_wf`, and
  `WfM.fun_sub_under_head_replace_from_body_wf`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WfM.sub_head_replace_from_payloads`, a constructor-level head
  replacement packager for `WfM` that wires leaf, `Wf-App`, and
  `Wf-Fun` cases to explicit recursive well-formedness,
  equivalence-preservation, and subtype-residual payloads. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WfM.replaceAt_sub_from_payloads`, the arbitrary-depth `replaceAt`
  analogue of the constructor-level `WfM` replacement packagers. It
  exposes the recursive body, equivalence-preservation, and
  well-subtyping-star subtype residual payloads explicitly. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added
  `WfM.sub_under_head_replace_from_payloads`, the preserved-head
  analogue of the constructor-level `WfM` replacement packager. This
  supports recursive binder descent while the changed `.sub` entry
  remains in the tail. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added structural subtype
  residual wrappers embedding transported raw `Ms-App` and `Ms-Fun`
  replacement chains into well-subtyping stars:
  `WSubMStar.app_replaceAt_sub_from_operator_to_star`,
  `WSubMStar.app_sub_head_replace_from_operator_to_star`,
  `WSubMStar.fun_replaceAt_sub_from_body_fixed_bound_to_star`, and
  `WSubMStar.fun_replaceAt_sub_from_body_changed_bound_to_star`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added under-head and
  binder-recursive `Ms-App` well-subtyping wrappers
  `WSubMStar.app_sub_under_head_replace_from_operator_to_star` and
  `WSubMStar.app_replaceAt_sub_from_body_operator_to_star`, packaging
  already transported operator subtype chains below preserved binders.
  No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added stack-sensitive changed-head
  `Ms-FOp` residual wrappers
  `MSubRedStar.fOp_sub_head_replace_from_body` and
  `MSubRedStar.fOp_sub_head_replace_from_body_replaceAt`, packaging the
  non-empty-stack `FOp` body residual at the direct head and recursive
  body `replaceAt 1` shapes. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added
  `MEqRed.pro_equ_head_replace_succ`, the non-head `Me-Pro` replacement
  case. It uses the new nonzero equivalence-lookup transport and a
  recursively replaced bound reduction, isolating the only remaining
  `Me-Pro` obstruction at the changed head index `0`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnReductions.lean` — added constructor rebuilders for
  innermost `.equ`-head replacement once recursive premises have already
  been replaced: `MEqRed.app_equ_head_replace`,
  `MEqRed.fun_equ_head_replace`, `MEqRed.bet_equ_head_replace`,
  `MEqRed.fOp_equ_head_replace`, `MSubRed.equ_equ_head_replace`,
  `MSubRed.app_equ_head_replace`, `MSubRed.fun_equ_head_replace`, and
  `MSubRed.fOp_equ_head_replace`. These make the eventual structural
  replacement induction explicit at constructor boundaries. No axiom-count
  change.
* `Pss/Context/DeBruijn.lean`, `Pss/Mpss/DeBruijnReductions.lean` —
  added `.equ`-head index-0 lookup inversions and
  `MEqRed.pro_equ_head_zero_residual`. The changed-head `Me-Pro` case
  is now exposed as a precise residual reducing from the old shifted
  head bound, rather than hidden inside a failed replacement attempt. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msub_equ_head_old_bound_to_new_bvar0`, which joins the old shifted
  head bound with the new `bvar 0` under a changed `.equ` head, assuming
  the old-to-new head equivalence has been lifted to the same residual
  stack. This identifies the remaining stack-sensitive lift needed for
  the head `Me-Pro` residual. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the converse
  `msub_equ_head_new_bvar0_to_old_bound`, which joins the new `bvar 0`
  back to the old shifted head bound using the same common reduct. This
  supplies the opposite diagrammatic edge needed when a residual `Me-Pro`
  appears as the source side of a replacement proof. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubStar_equ_head_new_bvar0_to_replaced_residual`, which composes the
  converse head bridge with a recursively replaced old-bound residual
  chain. This is the direct consumer shape for changed-head `Me-Pro`
  residuals in structural replacement. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_pro_residual_handler_of_replacement`, a canonical handler
  builder for the head `Me-Pro` replacement residual: it takes the
  old-to-new stack lift plus a recursive replacement of the old-bound
  residual and returns the handler expected by the equivalence splitter.
  No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_pro_tail_handler_of_replacement`, the canonical
  non-head `Me-Pro` handler for innermost `.equ` replacement. It rebuilds
  the shifted variable through the new head and composes with the
  recursively replaced looked-up-bound chain. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added stack-stable
  top-level equivalence lifts under a changed `.equ` head for reflexive,
  `Me-Top`, `Me-Var`, and `Me-TAp` shapes. These are the first true cases
  of the stack-sensitive lift needed by `msub_equ_head_old_bound_to_new_bvar0`;
  `Me-Fun`, `Me-Bet`, and recursive `Me-App` remain residual. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_stack_lift_app`, the recursive `Me-App` constructor for
  stack-sensitive lifting under a changed `.equ` head. The lift now
  reduces application steps to the expected operator and argument lift
  premises. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_stack_lift_pro`, the recursive `Me-Pro` constructor for
  variables from the original context. The changed `.equ` head shifts the
  variable index to `i + 1`; the looked-up bound reduction is supplied as
  the recursive lift premise. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — split the changed-head
  `Me-Fun` stack lift into `meq_equ_head_stack_lift_fun_nil` for the
  empty residual stack and `meq_equ_head_stack_lift_fun_cons_of_fop_body`
  for nonempty stacks, where the lifted abstraction is rebuilt through
  `Me-FOp` with an explicit operand-headed body premise. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_stack_lift_bet`, the recursive `Me-Bet` constructor for
  stack-sensitive lifting under a changed `.equ` head. The helper exposes
  the shifted body and empty-stack argument premises needed to rebuild the
  beta step, with the target normalized by the existing substitution-shift
  lemma. No axiom-count change.
* `Pss/Context/DeBruijn.lean` and `Pss/Mpss/DeBruijnReductions.lean` —
  added under-head `.equ` replacement prevalidity transport, lookup
  facts, and non-residual reduction constructors for `Me-Top`, `Me-Var`,
  `Me-TAp`, `Me-Pro` at the preserved head and indices `2+`, `Ms-Pro`,
  and `Ms-Top`. These support recursive replacement below a preserved
  binder while keeping the changed `.equ` entry one level down; the
  equivalence lookup at index `1` is exposed as
  `MEqRed.pro_equ_under_head_one_residual`. No axiom-count change.
* `Pss/Mpss/DeBruijnReductions.lean` — added constructor rebuilders for
  under-head `.equ` replacement after recursive premises have already
  been replaced: `MEqRed.app_equ_under_head_replace`,
  `MEqRed.fun_equ_under_head_replace`, `MEqRed.bet_equ_under_head_replace`,
  `MEqRed.fOp_equ_under_head_replace`, `MSubRed.equ_equ_under_head_replace`,
  `MSubRed.app_equ_under_head_replace`, `MSubRed.fun_equ_under_head_replace`,
  and `MSubRed.fOp_equ_under_head_replace`. These are the preserved-head
  counterparts to the innermost replacement rebuilders. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msub_equ_under_head_old_bound_to_new_bvar1`, the one-level-deeper
  analogue of `msub_equ_head_old_bound_to_new_bvar0`. It joins the old
  shifted under-head `.equ` bound to the new `bvar 1`, assuming the
  old-to-new bound equivalence has already been lifted to the same
  preserved-head residual stack. Also added
  `meq_equ_under_head_stack_lift_from_equ_head_lift`, which obtains that
  preserved-head old-to-new premise by weakening an existing changed-head
  stack lift one binder deeper, and
  `msub_equ_under_head_old_bound_to_new_bvar1_of_equ_head_lift`, which
  composes the weakening with the residual bridge. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the converse
  `msub_equ_under_head_new_bvar1_to_old_bound`, the preserved-head
  analogue for the under-head residual at index `1`. It joins `bvar 1`
  back to the old doubly shifted bound using the new doubly shifted bound
  as common reduct. Also added
  `msub_equ_under_head_new_bvar1_to_old_bound_of_equ_head_lift`, the
  composed form that weakens a changed-head old-to-new lift and immediately
  applies the converse bridge. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubStar_equ_under_head_new_bvar1_to_replaced_residual`, the under-head
  analogue that composes the converse `bvar 1` bridge with a recursively
  replaced old-bound residual chain. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_under_head_pro_residual_handler_of_replacement`, the
  preserved-head analogue of the canonical `Me-Pro` residual handler
  builder for index `1`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added preserved-head
  non-residual `Me-Pro` handler builders
  `meq_equ_under_head_pro_zero_handler_of_replacement` and
  `meq_equ_under_head_pro_tail_handler_of_replacement`, covering index
  `0` and indices `2+` respectively. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added canonical `Ms-App`
  handler builders `msub_equ_head_app_handler_of_operator_replacement` and
  `msub_equ_under_head_app_handler_of_operator_replacement`, lifting
  recursive operator replacement chains through fixed-argument application
  for innermost and preserved-head `.equ` replacement. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added canonical `Ms-Fun`
  handler builders `msub_equ_head_fun_handler_of_raw_replacements` and
  `msub_equ_under_head_fun_handler_of_raw_replacements`, packaging raw
  bound-equivalence and body-subtype replacements into the handler shape
  expected by the subtype replacement splitters. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added canonical `Ms-FOp`
  handler builders `msub_equ_head_fop_handler_of_body_replacement` and
  `msub_equ_under_head_fop_handler_of_body_replacement`, lifting recursive
  body replacement chains through `FOp` for innermost and preserved-head
  `.equ` replacement. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added canonical equivalence
  replacement handler builders for `Me-App`, `Me-Fun`, and `Me-Bet`:
  `meq_equ_head_app_handler_of_raw_replacements`,
  `meq_equ_under_head_app_handler_of_raw_replacements`,
  `meq_equ_head_fun_handler_of_raw_replacements`,
  `meq_equ_under_head_fun_handler_of_raw_replacements`,
  `meq_equ_head_bet_handler_of_raw_replacements`, and
  `meq_equ_under_head_bet_handler_of_raw_replacements`. These package raw
  recursive replacements into the handler shape expected by the equivalence
  replacement splitters. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added canonical `Me-FOp`
  handler builders `meq_equ_head_fop_handler_of_body_replacement` and
  `meq_equ_under_head_fop_handler_of_body_replacement`, combining a raw
  bound-equivalence replacement with a diagrammatic recursive body
  replacement under the preserved operand head. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added composite subtype
  replacement wrappers `msubRed_equ_head_replace_from_replacements` and
  `msubRed_equ_under_head_replace_from_replacements`, wiring the canonical
  `Ms-App`/`Ms-Fun`/`Ms-FOp` handlers into the one-step subtype splitters
  while keeping the recursive replacement premises explicit. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added composite equivalence
  replacement wrappers `meqRed_equ_head_replace_from_replacements` and
  `meqRed_equ_under_head_replace_from_replacements`, wiring the canonical
  `Me-App`/`Me-Fun`/`Me-Bet`/`Me-FOp` handlers into the one-step
  equivalence splitters while keeping the lookup-sensitive `Me-Pro`
  residual handlers explicit. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added generic chain consumers
  `msubRedStar_replace_from_step_replacement` and
  `meqRedStar_replace_from_step_replacement`, which compose per-step
  diagrammatic replacements across subtype/equivalence reduction stars. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added star-level subtype
  replacement wrappers `msubRedStar_equ_head_replace_from_replacements` and
  `msubRedStar_equ_under_head_replace_from_replacements`, specializing the
  generic chain consumer to the composed one-step subtype replacement
  wrappers. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added star-level equivalence
  replacement wrappers `meqRedStar_equ_head_replace_from_replacements` and
  `meqRedStar_equ_under_head_replace_from_replacements`, specializing the
  generic chain consumer to the composed one-step equivalence replacement
  wrappers while retaining explicit `Me-Pro` residual premises. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRed_equ_head_shifted_replace_from_replacements`, a shifted-stack
  equivalence replacement wrapper that wires the canonical head and non-head
  `Me-Pro` handlers into the composed one-step replacement path. This is the
  stack shape used by recursive `FOp` body residuals. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRedStar_equ_head_shifted_replace_from_replacements`, the chain-level
  shifted-stack counterpart that composes the same wired `Me-Pro`
  replacement over equivalence stars. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRed_equ_under_head_replace_with_pro_from_replacements`, wiring all
  under-head `Me-Pro` cases (preserved-head index `0`, changed-entry
  residual index `1`, and tail indices `2+`) into the composed equivalence
  replacement path. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRedStar_equ_under_head_replace_with_pro_from_replacements`, the
  chain-level counterpart that composes the same under-head `Me-Pro`
  replacement package over equivalence stars. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added shifted-stack subtype
  replacement wrappers `msubRed_equ_head_shifted_replace_from_replacements`
  and `msubRedStar_equ_head_shifted_replace_from_replacements`, using the
  shifted equivalence replacement package for `Ms-Equ` branches and exposing
  only recursive constructor replacements. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_body_fOp_msub_replacements`, a
  diagrammatic variant of the changed-argument structural application
  commutation package that consumes `MSubStar` body replacements directly.
  This matches the output of the de Bruijn replacement splitters, rather
  than requiring raw `MSubRedStar` residual replacements. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements`, wiring the
  diagrammatic `FOp` commutation endpoint to the shifted changed-head
  replacement packages for both equivalence-derived and direct subtype body
  residuals. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_stack_lift_from_handlers`, a one-step splitter for lifting
  empty-stack equivalence reductions under a changed `.equ` head and
  arbitrary residual stack. Stable leaves are discharged; recursive
  constructor cases and the nonempty-stack `Me-Fun` lift are explicit
  handler obligations. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added canonical handler
  builders for the changed-head stack-lift splitter:
  `meq_equ_head_stack_lift_pro_handler_of_replacement`,
  `meq_equ_head_stack_lift_app_handler_of_replacements`,
  `meq_equ_head_stack_lift_fun_nil_handler_of_replacements`,
  `meq_equ_head_stack_lift_fun_cons_handler_of_replacements`, and
  `meq_equ_head_stack_lift_bet_handler_of_replacements`. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_stack_lift_from_replacements`, wiring the canonical
  stack-lift handlers into the changed-head stack-lift splitter and leaving
  only recursive lift premises explicit. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added chain-level stack-lift
  helpers `meqRedStar_equ_head_stack_lift_from_step_lift` and
  `meqRedStar_equ_head_stack_lift_from_replacements`, composing the
  changed-head equivalence stack lift over `MEqRedStar` chains. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_lifted_shifted_fOp_replacements`,
  deriving the shifted old-to-new argument equivalence for the diagrammatic
  `FOp` commutation endpoint from `hEqArg` via the changed-head stack-lift
  package. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRed_equ_under_head_shifted_replace_from_equ_head_lift` and
  `meqRedStar_equ_under_head_shifted_replace_from_equ_head_lift`, wiring
  under-head shifted equivalence replacement to an already lifted changed-head
  old-to-new equivalence. These wrappers derive the doubly shifted
  `Me-Pro` residual bridge under the preserved head. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `msubRed_equ_under_head_shifted_replace_from_equ_head_lift` and
  `msubRedStar_equ_under_head_shifted_replace_from_equ_head_lift`, the
  subtype counterparts that reuse the under-head shifted equivalence package
  for `Ms-Equ` branches and compose over subtype-reduction chains. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added tail-stack variants
  `meqRed_equ_under_head_shifted_replace_from_tail_lift`,
  `meqRedStar_equ_under_head_shifted_replace_from_tail_lift`,
  `msubRed_equ_under_head_shifted_replace_from_tail_lift`, and
  `msubRedStar_equ_under_head_shifted_replace_from_tail_lift`. These expose
  the form needed by recursive `FOp` body replacements: the old-to-new
  changed-head equivalence is supplied at the preserved head's tail stack and
  weakened under that head locally. No axiom-count change.
* `Pss/Context/DeBruijn.lean` — added `Stack.shift_eq_cons_inv` plus
  equality-based `PrevalidExt.tail_of_eq_cons` and
  `PrevalidExt.head_scoped_of_eq_cons` extractors. These support future
  `FOp` residual proofs that learn non-empty stack shape from an equality
  against `Stack.shift`. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_shifted_fop_body_handler_from_tail_lifts` and
  `msub_equ_head_shifted_fop_body_handler_from_tail_lifts`, packaging the
  `FOp` body handlers required by shifted changed-head replacement from
  tail-stack old-to-new lifts plus explicit recursive body obligations. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_shifted_fOp_tail_lifts`, a shifted
  changed-argument structural application commutation wrapper that builds
  the recursive `FOp` body handlers from tail-stack old-to-new lifts before
  invoking `commute_appAbs_structApp_eqStep_of_shifted_fOp_replacements`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_argument_stack_lifted_fOp_tail_lifts`,
  deriving both the top-level shifted old-to-new argument equivalence and
  the recursive `FOp` tail old-to-new equivalences from a single reusable
  argument stack-lift function. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meq_equ_head_stack_lift_function_from_replacements`, a function-valued
  changed-head stack lift that packages the canonical handlers for every
  residual tail stack. This is the reusable source for argument stack-lift
  functions consumed by the `FOp` tail commutation wrappers. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRedStar_equ_head_stack_lift_function_from_replacements`, the
  chain-level function-valued counterpart for reusable changed-head stack
  lifts over `MEqRedStar` chains. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRedStar_equ_head_stack_lift_function_from_step_lift`, a generic
  function-valued chain lift over `MEqRedStar` from a tail-polymorphic
  one-step lift. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added generic function-valued
  chain consumers `msubRedStar_replace_from_step_replacement_function` and
  `meqRedStar_replace_from_step_replacement_function`, composing
  tail-polymorphic source chains with tail-polymorphic one-step replacement
  functions. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added function-valued shifted
  head replacement wrappers
  `meqRedStar_equ_head_shifted_replace_function_from_replacements` and
  `msubRedStar_equ_head_shifted_replace_function_from_replacements`, packaging
  shifted replacement over every residual tail stack. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added function-valued
  under-head shifted replacement wrappers
  `meqRedStar_equ_under_head_shifted_replace_function_from_tail_lift` and
  `msubRedStar_equ_under_head_shifted_replace_function_from_tail_lift`,
  packaging tail-lift replacements while deriving the new-tail prevalidity
  and preserved-head context replacement locally. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added function-valued
  under-head shifted replacement wrappers from changed-head lifts,
  `meqRedStar_equ_under_head_shifted_replace_function_from_equ_head_lift`
  and
  `msubRedStar_equ_under_head_shifted_replace_function_from_equ_head_lift`.
  These consume tail-polymorphic changed-head old-to-new lifts directly at
  the doubly shifted under-head stack. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `meqRedStar_equ_under_head_replace_with_pro_function_from_replacements`,
  the function-valued form of the under-head equivalence replacement with
  canonical `Me-Pro` handlers wired at every residual stack. No axiom-count
  change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added unshifted base
  replacement function wrappers
  `msubRedStar_equ_head_replace_function_from_replacements`,
  `msubRedStar_equ_under_head_replace_function_from_replacements`,
  `meqRedStar_equ_head_replace_function_from_replacements`, and
  `meqRedStar_equ_under_head_replace_function_from_replacements`, packaging
  the fixed-stack replacement wrappers over every residual stack. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added the subtype companion
  to under-head replacement with canonical `Me-Pro` handlers,
  `msubRedStar_equ_under_head_replace_with_pro_from_replacements`, plus
  the function-valued
  `msubRedStar_equ_under_head_replace_with_pro_function_from_replacements`.
  No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `StrongCommutes.pro_any`, the full de Bruijn Lemma-1 `Ms-Pro × Me-*`
  source cell. The `Me-Var` branch closes by the subtype binding, and the
  `Me-Pro` branch is impossible by context binding-kind uniqueness. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `EqDiamonds.bvar_any_of`, the full de Bruijn Lemma-2 variable-source
  cell. It combines the `Me-Var`/`Me-Pro` branches and delegates recursive
  `Me-Pro × Me-Pro` to the local bound diamond. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `StrongCommutes.bvar_any_of`, the full de Bruijn Lemma-1 variable-source
  cell. It combines `Ms-Pro`, `Ms-Equ`, and `Ms-Top`; the `Ms-Equ` branch
  delegates to the local equivalence diamond. No axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added prevalidity-recovering
  variable-source wrappers `EqDiamonds.bvar_any` and
  `StrongCommutes.bvar_any`, so future case-grid callers can consume the
  reduction steps directly while retaining the existing `_of` forms. No
  axiom-count change.
* `Pss/Mpss/DeBruijnTransitivityElim.lean` — added
  `commute_appAbs_structApp_eqStep_of_argument_replacement_fOp_tail_lifts`,
  which builds the reusable argument stack-lift function from canonical
  changed-head replacement premises before invoking the argument-stack-lifted
  `FOp` commutation wrapper. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added constructor inversions
  `WfM.fun_inv` and `WfM.app_inv` for the de Bruijn well-formedness
  judgment. `WfM.app_inv` returns a `Sigma` witness because the
  underlying well-subtyping stars are Type-valued. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added context-prevalidity
  extractors for all five de Bruijn well-formed judgments:
  `WfM.prevalid`, `WSubM.prevalid`, `WSubMStar.prevalid`,
  `WEquM.prevalid`, and `WEquMStar.prevalid`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added derived-prevalid insertion
  wrappers `WfM.insertAt'`, `WSubM.insertAt'`, `WSubMStar.insertAt'`,
  `WEquM.insertAt'`, and `WEquMStar.insertAt'`. These are convenience
  forms of the existing `insertAt` lemmas. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added transitive
  well-equivalence utilities: `WEquMStar.symm` and
  `WEquMStar.toWSubMStar`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added endpoint well-formedness
  extractors for de Bruijn transitive well-subtyping/equivalence:
  `WSubMStar.wf_left`, `WSubMStar.wf_right`, `WEquMStar.wf_left`, and
  `WEquMStar.wf_right`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added paired endpoint
  well-formedness extractors `WSubMStar.wf_pair` and
  `WEquMStar.wf_pair`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added reflexive empty-stack
  reduction bridges from well-formed terms: `WfM.MEqRed_refl` and
  `WfM.MSubRed_refl`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added single-step endpoint
  extension helpers for de Bruijn transitive well-subtyping:
  `WSubMStar.extend_left_via_MEqRed_fwd` and
  `WSubMStar.extend_right_via_MEqRed_back`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added matching single-step
  endpoint extension helpers for de Bruijn transitive well-equivalence:
  `WEquMStar.extend_left_via_MEqRed_fwd` and
  `WEquMStar.extend_right_via_MEqRed_back`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added the single-step subtype
  left-endpoint extension helper for de Bruijn transitive well-subtyping:
  `WSubMStar.extend_left_via_MSubRed_fwd`. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added direct embeddings from
  well-formed empty-stack reductions into de Bruijn transitive
  well-subtyping/equivalence: `WSubMStar.of_MEqRed_fwd`,
  `WSubMStar.of_MEqRed_back`, `WSubMStar.of_MSubRed_fwd`,
  `WEquMStar.of_MEqRed_fwd`, and `WEquMStar.of_MEqRed_back`. No
  axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added conditional chain
  embeddings from empty-stack reduction stars into de Bruijn transitive
  well-formed relations: `WSubMStar.of_MEqRedStar_fwd`,
  `WSubMStar.of_MEqRedStar_back`, `WSubMStar.of_MSubRedStar_fwd`,
  `WEquMStar.of_MEqRedStar_fwd`, and `WEquMStar.of_MEqRedStar_back`.
  Each requires an explicit stepwise `WfM`-preservation premise, avoiding
  the known false unrestricted subject-reduction statement. No axiom-count
  change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added conditional
  well-formedness propagation helpers for empty-stack reduction stars:
  `MEqRedStar.wf_right_of`, `MSubRedStar.wf_right_of`,
  `MEqRedStar.wf_pair_of`, and `MSubRedStar.wf_pair_of`. These also
  require explicit stepwise `WfM` preservation. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added conditional endpoint
  extension helpers along empty-stack equivalence-reduction chains:
  `WSubMStar.extend_left_via_MEqRedStar_fwd`,
  `WSubMStar.extend_right_via_MEqRedStar_back`,
  `WEquMStar.extend_left_via_MEqRedStar_fwd`, and
  `WEquMStar.extend_right_via_MEqRedStar_back`. These require explicit
  stepwise `WfM` preservation. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added the directed conditional
  left-endpoint extension helper along empty-stack subtype-reduction
  chains: `WSubMStar.extend_left_via_MSubRedStar_fwd`. This requires
  explicit stepwise `WfM` preservation. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added right-endpoint forward
  subtype-reduction extension helpers for de Bruijn transitive
  well-subtyping: `WSubMStar.extend_right_via_MSubRed_fwd` and
  `WSubMStar.extend_right_via_MSubRedStar_fwd`. The chain helper keeps
  the same explicit stepwise `WfM` preservation premise as the matching
  left-endpoint subtype-chain extension. No axiom-count change.
* `Pss/Mpss/DeBruijnWellFormed.lean` — added endpoint-only embeddings
  and endpoint extensions for empty-stack equivalence-reduction chains:
  `WSubM.of_MEqRedStar_fwd`, `WSubM.of_MEqRedStar_back`,
  `WEquM.of_MEqRedStar_fwd`, `WEquM.of_MEqRedStar_back`,
  `WSubMStar.of_MEqRedStar_fwd_of_wf`,
  `WSubMStar.of_MEqRedStar_back_of_wf`,
  `WEquMStar.of_MEqRedStar_fwd_of_wf`,
  `WEquMStar.of_MEqRedStar_back_of_wf`,
  `WSubMStar.extend_left_via_MEqRedStar_fwd_of_wf`,
  `WSubMStar.extend_right_via_MEqRedStar_back_of_wf`,
  `WEquMStar.extend_left_via_MEqRedStar_fwd_of_wf`, and
  `WEquMStar.extend_right_via_MEqRedStar_back_of_wf`. These use the
  existing `WSubM`/`WEquM` chain constructors and need only endpoint
  well-formedness, not stepwise preservation. No axiom-count change.

**Session 2026-05-04 (iters 1–7) infrastructure shipped:**
* `Lemma_32_AsymmetricEqu` (Pss/Mpss/AvoidsPro.lean:1010, commit
  `449fea0`) — asymmetric extension of `Lemma_32_ReductionUnderSubst_Eq_OfEqu`
  (substitutes different terms `v` and `v'` mediated by `MEqRed Γ [] v v'`).
  Counts as INACTIVE: not yet wired into any headline closure.
* `noVarX` Bool predicate + `noVarX_refl` theorem (commit `d427927`).
* `MEqRed.derSize` + strict-decrease lemmas (Pss/Mpss/MEqRedSize.lean,
  commit `a510bbc`).
* `Term.size` infrastructure (Pss/Syntax/LocallyNameless.lean, commit
  `fdd3f24`).
* **`Lemma_2_DiamondMEqRed_core` refactored to `termination_by structural h₁`**
  (commit `05fcb26`) — KEY ARCHITECTURAL BREAKTHROUGH. Body sub-derivations
  of `MEqRed.fOp`-shaped `hu` are now reachable via direct recursive
  `_core` calls. Confirmed in iter 6 (commit `09cbb97`) but blocked at
  the descent step (avoidance witness on body-diamond's output).
* `MEqRed.avoidsAllStray` + per-constructor preservation lemmas (5/8
  arms, commit `d881ed6`) — iter-7 motive-strengthening foundations.

**Iter-8+ next attack:** complete the cofinite-arm `avoidsAllStray`
preservation (bet/fun_/fOp), then strengthen `_core`'s output motive to
include `avoidsAllStray` witnesses. With output-side avoidance, the
descent step in `Lemma_2_inline_app_bet_residual_axiom` becomes possible
via the new `noVarX`/`avoidsPro`-equipped `Lemma_32_AsymmetricEqu`.

**Session 2026-05-04 (iters 8–13) — head-removal infrastructure shipped:**
The iter-8+ avoidsAllStray cofin-arm completion was deferred in favor
of a different unblock path: head-removal functor `MEqRed.strip_equ_head`
+ template-aware descent functor `descend_body_equ`.
* `Pss/Mpss/Renaming.lean` §10 — `Prevalid.equ_head_remove_mid`,
  `PrevalidExt.equ_head_remove_mid`, `Ctx.AvoidsBoundFv` predicate,
  `_y_notin_fv_lookupEqu_under_avoid` (commit `abea6a7`, iter 8).
* `Pss/Mpss/AvoidsPro.lean` §2.8 — `avoidsFv` Bool predicate +
  per-constructor simp lemmas (commit `4073b46`, iter 9).
* `Pss/Mpss/Renaming.lean` §10.3 — `MEqRed.strip_equ_head` head-removal
  functor (commit `2a45008`, iter 10). Mirror of `equ_head_replace`.
* `Pss/Mpss/Diamond.lean` — iter-11 blocker analysis on
  `Lemma_2_inline_app_bet_residual_axiom` (commit `4a2d755`):
  `strip_equ_head` cannot be directly applied to body-IH outputs
  whose source contains the binder being stripped (avoidsFv at the
  outermost source mention always fails). Architectural finding: paper
  sidesteps via α-conversion on named binders; LN encoding makes the
  obligation explicit.
* `Pss/Mpss/Renaming.lean` §11 — `descend_body_equ` template-aware
  descent functor:
  - **Phase A** (commit `189efe7`, iter 12): `body = .bvar 0` leaf case
    — `MEqRed.descend_body_equ_bvar0`. Avoids the trap by using the
    paper's "moreover" clause (`avoidsPro h y = true`) to rule out
    `MEqRed.pro y`, leaving only `MEqRed.var` whose target trivially
    rewrites to `.fvar z` under the requested substitution.
  - **Phase B** (commit `3795a4f`, iter 13): non-binding template
    cases — `descend_body_equ_top` (body = `.top`),
    `descend_body_equ_fvar` (body = `.fvar w`, w ≠ y; consumes
    `strip_equ_head` on the `pro` arm).

**Session 2026-05-04 (iters 14–19) — descend_body_equ Phase B2/C/D shipped, audit found avoidsFv gap, uniform rebuild started:**

Iters 14–16 shipped `descend_body_equ` Phases B2/C/D in `Pss/Mpss/Renaming.lean` §11.4–§11.5 (commits `e0aa2c1`, `dcb0d5c`, `e0a2608`):
* **Phase B2** (iter 14, commit `e0aa2c1`): `body = .abs t inner` leaf at §11.4. Uses `strip_equ_head + subst_fresh` shortcut keyed off `avoidsFv h y = true`.
* **Phase C** (iter 15, commit `dcb0d5c`): assembled dispatcher at §11.5 with `rec_app` continuation parameter for the `.app` arm.
* **Phase D** (iter 16, commit `e0a2608`): total functor by adding `descend_body_equ_app` leaf at §11.4b parallel to §11.4. Generalizes the §11.4 strip+subst pattern.

**Iter-17 audit (§11.6, commit `9e601ab`) confirmed a load-bearing gap.**
The §11.4–§11.5 functor takes `avoidsFv h y = true` as a premise — and **the headline consumer cannot satisfy it**. The body-IH source is `body'_dst^[y₀]`; whenever `body'_dst` syntactically mentions `.bvar 0`, the opening introduces `.fvar y₀` so `decide (y₀ ∉ fv source) = false`, hence `avoidsFv ≠ true`. Concrete counterexample: `body'_dst = .app (.bvar 0) .top`. The paper's "moreover" clause is `avoidsPro` (strictly weaker), which Phase A already uses correctly. The architectural fix is a stack-template-generalized functor `descend_body_equ_uniform` taking `avoidsPro` only.

**Iter-18 (§11.7, commit `a71e81f`) shipped foundations of the uniform functor:**
* `_PrevalidExt_descend_under_equ_head_template` (~80 lines) — the prevalid-side helper that descends `PrevalidExt` under stack-template y-freshness premises plus `z ∈ Γ.dom`.
* `_descend_body_equ_uniform_bvar0_aux` (~15 lines) — auxiliary cases-elim pattern (workaround for Lean 4's dependent-elim quirk on non-variable stack expressions).
* `MEqRed.descend_body_equ_uniform_bvar0` (~30 lines) — the bvar 0 leaf at the new uniform signature.

Iter-18 finding: **`hz_Γ : z ∈ Γ.dom` is mathematically required** (not bookkeeping) — the output stack `s_tmpl.map (·^[z]) ++ s_outer` carries z-dependence whenever `s_tmpl` has bvar-0-mentioning templates, and the prevalid-fv invariant demands `z ∈ Γ.dom`.

**Iter-19 (§11.7, commit `d2cf8b6`) extended the uniform functor:**
* §11.7.2 — `body = .top` leaf (full).
* §11.7.3 — `body = .fvar w` leaf, **var-arm only**. The `pro` arm is gated behind an `Empty` premise (honest scaffolding, NOT an axiom). Pro-arm blocker: `strip_equ_head` requires `avoidsFv` and `cofinDomFresh`, which the uniform signature deliberately excludes. An avoidsFv-free strip variant is needed — iter-20+ target.
* §11.7.4 — `body = .app a b` recursive case, **`MEqRed.app` constructor arm only** (open-recursion handlers as parameters). `MEqRed.tAp` and `MEqRed.bet` arms documented as deferred to iter-20+.

**Session 2026-05-04 (iters 20–28) — flat-stack descent shipped:**

Iters 20–25 shipped `descend_y_fresh_source_template` (`Pss/Mpss/Renaming.lean §11.9`)
covering all 8 MEqRed arms, completing the y-fresh-source descent functor
(commits `f4f05fd`, `6b4bdcb`, `26b78d7`, `112cd12`, `9c4375e`, `f074df3`).

Iter-26 (commit `34678c8`) assembled `MEqRed.descend_body_equ_uniform` (§11.10)
as a body-shape-dispatching wrapper. The `.bvar 0` / `.top` / `.fvar` /
`.bvar (n+1)` arms close cleanly; the `.app a b` and `.abs t inner` arms
were gated behind `Empty` premises (`hgate_app`, `hgate_abs`).

Iter-27 (commit `542c501`) sharpened the `.app` blocker analysis: the
gate cannot be discharged in template/outer-split form because the
operand `b` lacks `LC b` (only `LC (b^[y])`). Recommended path forward:
rewrite the descent functor with a flat substituted-stack output
`Stack.subst y (.fvar z) stk`, since `subst y (.fvar z) (b^[y]) = b^[z]`
when `y ∉ fv b` matches the `MEqRed.app` constructor rebuild.

**Iter-28 (commit `f6b53bd`) shipped the flat-stack descent functor.**
* `_MEqRed_descend_at_head_subst` (`Pss/Mpss/Renaming.lean §12`, internal)
  — substitution-form mirror of `Lemma_31_ReductionUnderSubst_Eq` for
  `.equ` head: source ctx `Γ₂ ++ ⟨y, α, .equ⟩ :: Γ₁`, output ctx
  `Ctx.subst y (.fvar z) Γ₂ ++ Γ₁`, handles `Me-Pro y` arms via
  `avoidsPro h y = true`'s `decide (yi ≠ y)` factor + `equBinds_split_equ`.
  All 8 MEqRed arms covered; `bet` uses `rename_stray`, `fun_` uses
  `rename_sub`, `fOp` uses `_MEqRed_rename_equ_no_fv` for the `pickFresh`
  → arbitrary-`yfresh` rename to navigate the alpha-equivariance trap.
* `MEqRed.descend_at_head` (caller-facing wrapper) — uses `hΓ₂_avoid` to
  bridge `Ctx.subst y (.fvar z) Γ₂ = Γ₂` for the headline use case
  (`Γ₂ = []`).

This is the iter-27-recommended stack-form descent functor. It supplants
the template/outer split: source can be y-occurring (e.g. `.fvar y` —
the body-`bvar 0` case), so the body-shape dispatch in
`descend_body_equ_uniform` becomes unnecessary at the consumer level.

**Iter-29 (commit `338b0e6`) shipped consumer-facing wrapper.**
`MEqRed.descend_body_equ_uniform_app` (`Pss/Mpss/Renaming.lean §12`,
caller-facing) — specializes `descend_at_head` to `Γ₂ = []` and rewrites
the substitution-form output back to the opening-form shape
`MEqRed Γ s (body^[z]) (Term.subst y (.fvar z) target)` expected by
Lemma 2 consumers. Bridges via `Stack.subst_fresh hy_souter` and
`Term.subst_open_fresh hy_body`. ~80 lines. No new axioms.

**Iter-30+ blocker: cofinite-z gap.** Audit during iter-29 dispatch
revealed that the discharge of `Lemma_2_inline_app_bet_residual_axiom`
(axiom #9) requires the body-descent to produce a *cofinite* output
shape `∀ y ∉ L', MEqRed Γ s (body'_dst^[y]) (body_join^[y])` for the
`MEqRed.bet` β-fire on the LHS chain. But `descend_body_equ_uniform_app`
requires `z ∈ Γ.dom` (inherited from `SubstOk Γ (.fvar z)` in
`_MEqRed_descend_at_head_subst`'s internal substitution step), while
the cofinite witness `y ∉ L'` is necessarily outside `Γ.dom`. The two
constraints are mutually exclusive.

**Iter-30+ candidate paths** to bridge the gap:
1. Extend `descend_body_equ_uniform_app` to handle out-of-scope `y`
   by first weakening Γ → `⟨y, .top, .sub⟩::Γ`, descending at `z = y`
   (now in scope), then post-stripping the temporary head binding.
   ~100-150 lines. Requires careful tracking of `Lemma_22_WeakeningMEqRed`
   and `strip_equ_head`-like infrastructure (already exists, but the
   composition is novel).
2. Replace cofinite output with a single-witness output and rebuild the
   cofinite shape via `MEqRed.rename_stray`. The rename functor requires
   both names outside `Γ.dom`, so this needs a trampoline through a
   widened ctx.
3. Reformulate `_MEqRed_descend_at_head_subst` to allow stray `z`
   directly, by relaxing the `SubstOk` premise. Architecturally cleanest
   but requires re-proving all 8 MEqRed arms with a different prevalidExt
   strategy. Largest scope.

The §11.4–§11.5 functor (avoidsFv-flawed) is RETAINED for now; iter-30+
retires it once the cofinite-z bridge lands and `descend_body_equ_uniform_app`
is consumed end-to-end.

**Iter-30 (commit forthcoming) — SPIKE result: all three paths are
fundamentally blocked.** Spiked Path 1 (the dispatch's recommended
trampoline). After Steps 1+2 (widen Γ → `⟨z, .top, .sub⟩::Γ` via
`Lemma_22_WeakeningMEqRed`, descend at z via the iter-29 wrapper
applied to widened ctx) the output lives at `MEqRed (⟨z, .top, .sub⟩::Γ)
s (body^[z]) (subst y (.fvar z) target)`. Step 3 (strip the synthetic
head) is **mathematically impossible**: the descended source `body^[z]`
mentions z (when body has bvar 0). A `.sub` (or `.equ`) head strip
that descends into `MEqRed.app`'s sub-derivation reaches stack
`(b^[z]::st)` and demands `Term.fv (b^[z]) ⊆ Γ.dom`. But b^[z] mentions
z (when b has bvar 0), and z ∉ Γ.dom by hypothesis. The blocker is
**not** about Me-Pro lookups (which `.sub` strips would skip): it's
about the recursive PrevalidExt invariant in the `MEqRed.app`
constructor's stack-extension.

Path 2 (single-witness in-dom + rename to stray) is blocked because
`MEqRed.rename_stray` requires BOTH endpoints outside Γ.dom — and the
in-dom witness violates this. There is no `rename_internal_to_stray`
infrastructure, and Γ may be empty (no in-dom witness even exists).

Path 3 (relax SubstOk in `_MEqRed_descend_at_head_subst`) requires a
~500-800 line refactor of all 8 MEqRed arms with a different prevalid-
side strategy. Beyond iter-30 scope.

Detailed analysis lives at `Pss/Mpss/Renaming.lean §13` (iter-30 spike
section; no code added — analysis only). Sharpened plan for iter-31+:
two architectural levers actually unblock the gap.

**Iter-31+ — Lever A: Open-target descent.** Reformulate the descent
on the OPENED form of target. Take `h : MEqRed (⟨y, α, .equ⟩::Γ) s
(body^[y]) target` and produce `∀ y' ∉ L', MEqRed Γ s (body^[y'])
(target'^[y'])` where `target'` is reverse-engineered from `target`
(when `y ∉ fv body`, `target` factors as `target'^[y]` for a unique
y-fresh `target'`). Cost: ~600-1000 lines. Requires building a
canonical `Term.openInverse y target` function and proving the descent
is body-shape-sensitive.

**Iter-31+ — Lever B audit: existing `_MEqRed_rename_equ_no_fv` is
strictly weaker than required.** The plan agent in iter-31 (commit
`575747e`'s prep work) confirmed `_MEqRed_rename_equ_no_fv`
(Renaming.lean:1955) requires the target to be ALREADY factored as
`body'^[y]` with `y ∉ fv body'`. The consumer's body-IH output has no
such factorization — the join term `body₃` from `_core` is wholly
existential. Lever B's "rename_at_head with arbitrary target" would
need an extra ~500-800 lines (substitution-style on possibly-
y-mentioning targets) AND would still not address the consumer's
actual need (uniform `body_join`). **Lever B is dispreferred.**

**The deeper finding — `_core`'s body-IH is structurally accessible
already.** Iter-5 (commit `05fcb26`) added `termination_by structural
h₁`, so `_core`'s App arm CAN do `cases hu` and recurse on
`hbody_dst y hy` (a structural sub-tree of `hu = MEqRed.fOp ...`). The
body-IH was never the missing piece; the missing piece is the descent
of the body-diamond's join target back into y-fresh form for
`MEqRed.bet`'s body slot. **Lever A is the right tool.**

**Iter-31 (commit `575747e`) — Lever A Phase 1 SHIPPED.**
`Term.openInverse y target` (`Pss/Syntax/LocallyNameless.lean`,
+135 lines):
* `Term.openInverseAt y k` — close the `k`-th binding (alias for
  existing `Term.close_ k y`).
* `Term.openInverse y` — close at level 0.
* `Term.openInverse_open` — `(openInverse y target)^[y] = target`
  under `Term.LC target`. **This is the property the consumer needs.**
* `Term.openInverse_fresh` — identity when `y ∉ fv t`.
* `Term.openInverse_open_self` — round-trip `openInverse y (t^[y]) = t`
  when `y ∉ fv t`.
* `Term.openInverse_fv` — `fv (openInverse y t) ⊆ fv t \ {y}`.

Build green; headline axiom closures byte-identical to iter-30
(9 active axioms unchanged).

**Iter-32+ — Lever A Phase 2.** Build `MEqRed.openInverse_descend`:
the 7-arm MEqRed traversal that, given
`MEqRed (⟨y, α, .equ⟩::Γ) s (body^[y]) target_open` plus the moreover
clause (`avoidsPro h y = true`), produces a y-fresh `target` with
`target_open = target^[y]` AND a cofinite-y derivation
`∀ z ∉ Γ.dom, MEqRed Γ s (body^[z]) (target^[z])`. Estimated ~400-700
lines (the iter-31 plan's lemma signature for `openInverse_descend`).
With this, the App×Bet residual closes in ~80-150 lines: pick
canonical y₀, recurse `_core` on body, apply `openInverse_descend` to
extract uniform `body_join`, rebuild `MEqRed.bet`'s cofinite slot.

The §11.4–§11.5 functor (avoidsFv-flawed) is RETAINED for now; iter-30+
retires it once the cofinite-z bridge lands and `descend_body_equ_uniform_app`
is consumed end-to-end.

**Iter-32 Phase 2.0–2.4 — Lever A Phase 2 partial close.**
Phase 2.0 (commit `7c4b273`): shipped `MEqRed.openInverse_descend`
signature with all 8 arms `Empty`-gated (the function compiles but
each arm is a stub). Phase 2.1 (`adb6779`): closed `top` and `var`
arms. Phase 2.2 (`ebb78b3`): walled at WF on `pro` (Eq.rec cast). Phase
2.3 (`c0aa2d0`): refactored signature to take `hsrc : source = body^[y]`
explicitly; eliminated cast but exposed structural-recursion
WF rejection. Phase 2.4 (`dfd06b7`): refactored to `induction h
generalizing body` pattern (mirror of `_MEqRed_descend_at_head_subst`
§12); closed `pro` arm honestly without WF goals. Status entering
Phase 2.5: 3 of 8 arms closed (`top`, `var`, `pro`); 5 arms
(`tAp`, `app`, `bet`, `fun_`, `fOp`) still `Empty`-gated.

**Iter-32 Phase 2.5 — Lever A WALLS at the `tAp` arm (this iteration).**
Status: **Lever A's headline signature is mathematically false.**
A Lean-checked counterexample lands at `MEqRed.openInverse_descend`'s
`tAp` arm in `Pss/Mpss/Renaming.lean §15`
(`MEqRed.openInverse_descend_tAp_counterexample`). The structural
issue:

* `MEqRed.tAp`'s third premise is `Term.fv u ⊆ Γ.dom` for the
  operand `u` under `.top`. Inside `openInverse_descend`'s `tAp`
  arm, after body-shape inversion `body = .app .top body_u`, the
  output requires constructing `MEqRed Γ s (.app .top (body_u^[z])) .top`
  for stray `z ∉ Γ.dom`. The operand-fv premise becomes
  `Term.fv (body_u^[z]) ⊆ Γ.dom`. When `body_u = .bvar 0` (a
  legitimate input shape — passes `avoidsPro_tAp = true`,
  `cofinDomFresh_tAp = true`, and `fv (.fvar y) ⊆ insert y Γ.dom`),
  we get `body_u^[z] = .fvar z`, and the premise reduces to
  `{z} ⊆ Γ.dom`, which contradicts `z ∉ Γ.dom`.

* The output is uninhabited under any of the 8 `MEqRed`
  constructors: 7 fail by source/target shape mismatch, and the
  remaining `tAp` constructor's fv premise fails as above.

* **The wall is structural, not local to `tAp`.** Five
  `MEqRed` constructors carry fv-check premises (or stack-fv
  invariants) that must be reconciled with the post-rename
  bvar-0-mentioning sub-term: `tAp`, `app` (via the stack
  invariant on `v :: s`), `bet` (operand premise + body's
  bvar-0 occurrences in target), `fun_` and `fOp` (body
  recursion under sub-context whose dom contains `x`, not `z`).
  All five plausibly admit the same `body_u = .bvar 0`-style
  counterexample.

**Implication for the campaign:**
* Lever A as currently formulated is dead; the cofinite-z output
  promises something stronger than is true.
* The `Empty`-gated `tAp` / `app` / `bet` / `fun_` / `fOp` arms
  in `openInverse_descend` cannot be discharged honestly; the
  function survives only as a partial-defined function used by
  no caller (3 closed arms unblock no consumer).
* **Pivot path:** the de Bruijn refactor of `Term`, `MEqRed`,
  `MSubRed` is the next architectural lever. de Bruijn replaces
  the cofinite-z handle with a fresh-index handle that carries
  no fv constraint, eliminating the wall structurally. Cost
  estimate: multi-week refactor (~3000-5000 lines touched).
* Alternative pivot: a "dom-extending z" reformulation, where
  the descent functor's output context is `(z, αz, .equ) :: Γ`
  rather than bare `Γ`, permitting `z ∈ output ctx.dom`. This
  echoes the iter-30 wrapper's shape and may be Lever C.

The counterexample is shipped in `Pss/Mpss/Renaming.lean §15` and
its `#print axioms` reads `[propext, Quot.sound]` (no project-level
axioms — the un-inhabitability is constructively verified by
case-analysis on the supposed derivation).

**Post Type-LC refactor (Option B, branch `type-lc-experiment`):**
`avoidsPro_refl` (axiom #12 in the original audit) was discharged to a
real theorem in commit `64162c2` after lifting `Term.LC` from `Prop` to
`Type`. The 5 active β-residual axioms (#6, #7, #8, #9, #10) remain
because they require restructuring `Lemma_2_DiamondMEqRed_core`'s
induction scheme to a lex measure on `(Term.size t₀, avoidsPro-count)`
— a separate, multi-day refactor. The Type-LC refactor was the
prerequisite for that work but does not by itself complete it.

### Discharge plan for the β-residuals (post-Type-LC, next-session targets)

The β-residuals have a single shared blocker: `_core`'s `induction h₁`
fixes the IHs at the source-derivation's stack, which prevents the
App×App and β-step arms from cleanly closing across stack-head shifts
and term-substitutions. Concrete plan:

1. **`MEqRed.equ_head_replace` (new lemma).** Given `MEqRed (⟨y, α,
   .equ⟩ :: Γ) s u u'`, `MEqRed Γ [] α α'`, AND `avoidsPro h y = true`,
   produce `MEqRed (⟨y, α', .equ⟩ :: Γ) s u u'`. Structural recursion;
   `Me-Pro` arm is the discharge site for the `avoidsPro` premise (when
   `Me-Pro` looks up `equBinds y α`, the avoidsPro witness rules out
   `y = name-being-promoted`). With `avoidsPro_refl` now a real
   theorem, the closing tree's `MEqRed.refl` invocations satisfy
   `avoidsPro = true` automatically. Estimated ~150-200 lines.

2. **`MEqRed.stack_head_replace` (new lemma).** Given
   `MEqRed Γ (α :: s) u u'` and `MEqRed Γ [] α α'`, produce
   `MEqRed Γ (α' :: s) u u'`. Structural recursion; the `fOp` arm
   reduces to `MEqRed.equ_head_replace` (item 1) since the body's
   `.equ` head is `α`. Estimated ~100 lines on top of item 1.

3. **`Lemma_2_DiamondMEqRed_ctx_axiom` (single-step Ct-Stk discharge).**
   With items 1 and 2, the App×App `_inline_app` arm's use of
   `_ctx_axiom` (which is exactly a single Ct-Stk step) becomes
   directly provable: apply `MEqRed.stack_head_replace` to lift
   `hu'_w` and `hu₂_w` from stack `(v::s)` to stacks `(v'::s)` and
   `(v₂::s)` respectively. Eliminates `_ctx_axiom` from `_core`'s
   closure, which removes it from Theorems 3, 4, Lemma 1 / 2 closures.

4. **β-residual axioms (#6, #9, #10).** Threading the moreover-clause
   through `_core`'s App×App, App×Bet, Bet×* arms requires
   restructuring `_core` to either (a) thread an `avoidsPro` premise
   through every constructor case, OR (b) compute the moreover-clause
   as a separate property of `_core`'s output via a second induction.
   Path (b) is cleaner but requires items 1-3 to be in place first
   (the closing arms of `_core` invoke `MEqRed.refl`, whose `avoidsPro`
   is now `true` thanks to `avoidsPro_refl`). Estimated ~500-1000
   lines combined.

5. **`Lemma_1_inline_app_bet_residual` (#7) and `Lemma_1_ctx_axiom`
   (#6).** Mirror of the Lemma 2 work for the strong-commutativity
   diagram. Same approach with MSubRed in place of one of the MEqRed.

The `_inline_app`'s App×App use of `_ctx_axiom` is the single highest-
leverage target: discharging it (via items 1-3) eliminates
`_ctx_axiom` from ALL headline theorem closures (it remains only in
the explicit `Lemma_2_DiamondMEqRed_general` form which is paper-API
boilerplate, not a headline).

**Phase 5a complete (2026-05-03).** `AvoidsProUniv` Prop predicate +
per-constructor simp lemmas + bridge `AvoidsProUniv → avoidsPro = true`
+ `AvoidsProUniv_refl` shipped in `Pss/Mpss/AvoidsPro.lean §2.5`. This
is rename-stable infrastructure (universal quantification over cofinite
witnesses survives `L ↦ L'` widening, unlike the Bool `avoidsPro`'s
`pickFresh L` sample point) for the cofin* family.

**Phase 5b'/5c complete (2026-05-03).** Cast-invariance lemmas
(`AvoidsProUniv_subst_eq_dest/src/ctx/stack`) + master HEq form
(`AvoidsProUniv_eq_of_heq`/`AvoidsProUniv_cast`) shipped in
`Pss/Mpss/AvoidsPro.lean §2.5.1a`. Existence-form preservation
`AvoidsProUniv_subst_yz_stray_exists` shipped in `Pss/Mpss/Renaming.lean §7.0a`:
`∀ h huniv, ∃ h' (renamed), AvoidsProUniv h' x`. Built by parallel
structural induction; cofinite arms close via `body_each` Σ-existence
witnesses combined via `Classical.choose`. No new axioms.

Phase 5d: integrate the existence-form preservation into β-residual
discharge. Headline axiom counts unchanged by 5a/5b'/5c (infrastructure-
only).

**Phase 5e blocked (2026-05-03 — same date).** First attempt at consuming
Phase 5d's `stack_head_replace_univ_exists` to discharge the App×App
internal use of `Lemma_2_DiamondMEqRed_ctx_axiom` discovered an
**architectural gap** in the Type-aware MEqRed design:
`stack_head_replace_univ_exists` requires `CofinAvoidsProSelfUniv` on its
input derivation, which **cannot be supplied at the public Lemma 2 entry
point**. See `Pss/Mpss/Diamond.lean`'s `Lemma_2_DiamondMEqRed_ctx_axiom`
docstring (Phase 5e blocker section) for the full analysis. Headline
axiom counts unchanged. Alternative paths forward documented in the
docstring; none ship-ready.

**Phase 5f: option (a) "App×App restructure" viability analysis blocked
(2026-05-03 — same date).** A subsequent attempt explored four sub-variants
of restructuring `_inline_app`'s App×App arm to AVOID stack-head replacement
entirely (sidestepping the Phase 5e CAPSU population trap):
- **(a1)** "Diamond at u doesn't care about stack mismatches" — blocked.
  Closing `MEqRed Γ s (.app u' v') t₃` via constructor analysis FORCES
  `t₃ = .app w v_w` with operator sub-derivations at stacks `(v' :: s)` /
  `(v₂ :: s)`, not the IH-given `(v :: s)`. `MEqRed` is a parallel-reduction
  relation (not transitively closed), so composing derivations to bridge
  stack heads is unavailable.
- **(a2)** "Reduce v first, then close operator at common stack" — blocked.
  `_core` is structural-recursive on `h₁`, so `ihu` is FIXED at stack
  `(v :: s)` from `h₁`'s `.app` constructor signature. Any operator
  derivation at a different stack must be CONSTRUCTED via stack-head
  replacement, which is the Phase 5e wall.
- **(a3)** "Output CAPSU guarantee from `_core` motive without input CAPSU"
  — blocked. The Pro × Var case outputs `MEqRed.pro hpv₂ heq₁ hα₁`, whose
  CAPSU (by `CofinAvoidsProSelf_pro` simp) reduces to CAPSU on `hα₁`, a
  sub-derivation of input `h₁`. Output CAPSU still bottoms out at input
  CAPSU on `h₁/h₂` — same blocker as Phase 5e.
- **(a4)** "Ship analysis, propose option (b)" — selected.

The structural reason: `MEqRed.app`'s constructor co-fixes the operator's
stack-head and the operand's source as the SAME term `v`, so any closing
of two parallel reductions whose operands disagree must shift stack heads
somewhere in the closing tree. Stack-head replacement requires side
conditions the public API can't populate. See `Pss/Mpss/Diamond.lean`'s
docstring Phase 5f section for the four-paragraph analysis. Headline
axiom counts unchanged. Recommended next direction is the cross-codebase
Type-LC + alpha-aware MEqRed refactor (multi-day, preserves paper proof
structure but unblocks the rename-stable infrastructure end-to-end).

**Phase 5g.3b STRUCTURALLY IMPOSSIBLE (2026-05-03 — same date).** The
"alpha-aware MEqRed refactor" recommended at the end of Phase 5f was
attempted in Phase 5g.1/5g.2/5g.3a (uniform-cofinite constructor scaffold
+ ~127 call-site migration to `trivial` placeholders + extracting
`AvoidsProUniv` to its own file to break the import cycle).

Phase 5g.3b's plan was to replace the `(hUniform : True)` placeholder on
`MEqRed.bet/fun_/fOp` (and `MSubRed.fun_/fOp`) with the real

```
∀ x y (hx : x ∉ L) (hy : y ∉ L) (w : String),
    AvoidsProUniv (hbody x hx) w ↔ AvoidsProUniv (hbody y hy) w
```

via a `mutual inductive` block that lets `MEqRed` and (an inductively-
redefined) `AvoidsProUniv` cross-reference. The blocker analysis in
commit `60ab132` named two paths: (a) mutual block, (b) redefine
`AvoidsProUniv` structurally on Term shape.

A spike in `pss-20260503-235559` confirmed BOTH paths are dead:

* **Universe-mismatch in mutual block.** Lean 4 rejects a `mutual` block
  containing both a `Type`-valued and a `Prop`-valued `inductive` ("invalid
  mutually inductive types, resulting universe mismatch"). Forcing both
  to `Type` doesn't help — see next.
* **Mutual neighbor invisible in INDEX position.** Lean 4 rejects a
  `mutual` block where one inductive's INDEX or PARAMETER signature
  references another mutual neighbor by name ("unknown identifier
  'MEqRed_C'"). Mutual neighbors are visible inside CONSTRUCTOR
  ARGUMENT TYPES only. So `inductive AvoidsProUniv : MEqRed_C u v →
  String → Type` cannot live in the same mutual block as `MEqRed_C`.
* **"Structural-on-Term" path rejected.** `avoidsPro h x` is a property
  of which `Me-Pro` lookups the derivation tree takes; two derivations
  of the same source/target sequent can have radically different
  `Me-Pro` patterns (`var` vs `pro`-then-refl), so no Term-level
  predicate captures the same content.
* **External alpha-equivariance lemma fallback also fails.** The Plan
  agent's recommendation to replace constructor-baked uniformity with
  an externally-proved theorem `AvoidsProUniv_uniform_across_witnesses`
  is unsound for arbitrary `hbody` — `hbody : ∀ y ∉ L, MEqRed Γ st
  (body^[y]) (body'^[y])` is a function with no a priori uniformity
  guarantee. Two cofinite witnesses `y₁ ≠ y₂` can have `hbody y₁ _`
  and `hbody y₂ _` produced by completely different proof skeletons,
  in which case their `AvoidsProUniv` values disagree. The Phase 5b/5c
  existence-form lemmas (`AvoidsProUniv_subst_yz_stray_exists`) are
  provable because they CONSTRUCT a renamed derivation with the right
  property — they do NOT claim equality of avoidance values across the
  pre-existing function.

**Implication for the discharge campaign.** Phase 5g's premise — that
constructor-level uniformity can be added to `MEqRed`'s cofinite arms —
is false. The `True` placeholders shipped in 5g.1/5g.2 are dead weight;
they preserve no option value because the only useful replacement is
structurally inadmissible. The `(hUniform : True)` slots could be
reverted at the cost of churning ~127 call sites, but kept for now to
avoid regression risk — future iterations should remove them when
attacking another part of `Reductions.lean`.

**The honest path forward for the β-residual axioms** is one of:

1. **Existence-form composition (Lever A — Phase 5d's direction).**
   Use `AvoidsProUniv_subst_yz_stray_exists` and friends to construct
   closing trees existentially in β-residual proofs. Phase 5e/5f already
   showed this hits the App×App stack-shift trap at the public Lemma 2
   API. Could be revisited if the API can be extended to carry the CAPSU
   side conditions.
2. **Setoid quotient on derivations.** Quotient out non-uniform
   witnesses via an alpha-equivalence on derivations, then work in the
   quotient. Massive refactor; experimental viability.
3. **De Bruijn re-encoding.** Switch from cofinite quantification to
   uniform de Bruijn or nested-abstraction encoding. Massive cross-
   codebase refactor; loses paper-faithful binder structure.
4. **Accept axioms permanently.** Mark the β-residual axioms (and the
   ctx_axioms) as paper-permanent in the same vein as `Conjecture_8`,
   with a citation to the architectural-impossibility proof above.

None of (1)–(4) is single-iteration. The campaign needs strategic
input on which direction to commit to next.

> "Active" = currently in the transitive `#print axioms` dependency list
> of at least one headline theorem (Theorem 3, 4, 5; Lemma 1; Lemma 2).
> "Inactive" = no headline theorem depends on it; retained for
> documentation / paper-faithfulness / partial-discharge reasoning.

Run `nix develop --command lake build Pss.Sanity` to regenerate the
per-theorem dependency lists below.

---

## Headline theorem axiom dependencies (current)

The kernel axioms `propext`, `Quot.sound`, `Classical.choice` are common
to all five and elided below.

### `Theorem_3_TransitivityIsAdmissible`

* `Pss.Lemma_24_NarrowingMSubRed`
* `Pss.Lemma_1_ctx_axiom` *(private)*
* `Pss.Lemma_1_inline_app_bet_residual` *(private)*
* `Pss.Lemma_2_DiamondMEqRed_ctx_axiom` *(private)*
* `Pss.Lemma_2_inline_app_bet_residual_axiom` *(private)*
* `Pss.Lemma_2_inline_bet_residual_axiom` *(private)*

### `Theorem_4_Progress`

Same as Theorem 3 (Theorem 4 routes through transitivity-elim).

### `Theorem_5_Preservation`

* `Pss.Lemma_10_Inversion`
* `Pss.Lemma_24_NarrowingMSubRed`
* `Pss.Lemma_30_msPro_x_axiom`
* `Pss.Proposition_17_beta_axiom`

(Note: Theorem 5 does NOT depend on `Conjecture_8_*`, on
`Lemma_1_ctx_axiom`, or on the Lemma-2 residuals. The Wave-7 discharge
of Lemma 7 routes around Conjecture 8 via the WfM/WSubM/WSubMStar
mutual recursor.)

### `Lemma_1_StrongCommutativity`

Same as Theorem 3.

### `Lemma_2_DiamondMEqRed`

* `Pss.Lemma_2_DiamondMEqRed_ctx_axiom` *(private)*
* `Pss.Lemma_2_inline_app_bet_residual_axiom` *(private)*
* `Pss.Lemma_2_inline_bet_residual_axiom` *(private)*

---

## Permanent (paper-conjecture status)

### 1. `Conjecture_8_WellSubtypingContextIndependent`

* **File:** `Pss/Mpss/TypeSafety.lean`, line 141.
* **Statement (verbatim from paper p. 13):** For `Γ ⊢ u ≤*_wf t`, any
  covariant context `Co` such that both `Co[u]` and `Co[t]` are
  well-formed in `Γ` satisfies `Γ ⊢ Co[u] ≤*_wf Co[t]`.
* **Status:** Permanent. Open conjecture in the source paper; we mirror
  its open status here.
* **Paper:** Pasquale & García-Pérez 2024, §4 p. 13 (Conjecture 8).
* **Activity:** Currently UNUSED by any headline theorem. Wave 7's
  discharge of `Lemma_7_SubstitutionPreservesWf` was reworked to route
  around it via direct IH on the `WSubMStar` premises in the Wf-App
  case. Retained as a paper-faithful axiom for reference; if a future
  refactor reintroduces a use site, it can be re-cited here.
* **Discharge plan:** Closing this conjecture is a research-level
  metatheory result, not a proof-engineering exercise.
* **Estimated complexity:** Permanent / not a discharge target.

---

## Active outstanding (block discharged headline theorems)

These appear in the `#print axioms` closure of at least one headline
theorem.

### 2. `Lemma_24_NarrowingMSubRed`

* **File:** `Pss/Mpss/Narrowing.lean`, line 417 (axiom statement) and
  the post-axiom docstring §4 for the discharge progress.
* **Paper:** Appendix Lemma 24.
* **Statement:** Narrowing for `MSubRed`: if `MSubRed (Γ₂ ++ ⟨x, t', .sub⟩ :: Γ₁) st u v`
  and `Term.LC t` and `fv t ⊆ Γ₁.dom`, then
  `MSubRed (Γ₂ ++ ⟨x, t, .sub⟩ :: Γ₁) st u v`. (No prior chain `t → t'`
  required — the antecedent has been weakened from the paper's
  formulation.)
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1.
* **Discharge plan (2026-05, post-attempt-2):** The honest discharge
  takes an `msAvoidsPro h x = true` side condition (the paper's "no
  Ms-Pro on x" premise, captured by the Bool-valued `msAvoidsPro` in
  `Pss/Mpss/AvoidsPro.lean`). With the avoidance witness:
  1. Ms-Pro y arm: vacuous when y = x; else `_subBinds_narrow_neq`.
  2. Ms-Top, Ms-Equ, Ms-App: structural recursion via existing helpers.
  3. Ms-Fun arm: recurse at canonical sample
     `y0 := pickFresh (L ∪ fv body ∪ fv body' ∪ {x})` (the widened
     freshness set introduced by this commit's edit to `msAvoidsPro`),
     then build body at arbitrary z via `MSubRed.rename_sub` (no-fv
     rename in `Pss/Mpss/Renaming.lean`). NO alpha-equivariance.
  4. Ms-FOp arm: same shape as Ms-Fun, using
     `_MSubRed_rename_equ_no_fv` from `Pss/Mpss/Renaming.lean`.

  **Phase B (2026-05, this commit):** All 6 arms above are
  DISCHARGED in `_Lemma_24_NarrowingMSubRed_aux` (private,
  `Pss/Mpss/Narrowing.lean` lines 514-666). Modulo the avoidance
  witness wire-up at the call sites, the lemma is proved.
* **Wire-up status (2026-05, post Phase-B audit, agent_id:
  och-l24-wireup):** REMOVAL FROM HEADLINE CLOSURES IS BLOCKED.
  Auditing the two call sites of `Lemma_24_NarrowingMSubRed`:

  * `Pss/Mpss/Narrowing.lean:_N_lf2` (line 812). Used inside
    `Lemma_23_NarrowingWf` for the `WSubM.lf2` constructor. The
    surrounding `_N_motive_sub` motive does not thread an avoidance
    premise. The actual high-level consumer is `absBound` in
    `TypeSafety.lean:1058`, which calls `Lemma_23_NarrowingWf` on
    `hwfBody_old : WfM (⟨y, bound, .sub⟩ :: Γ) (body^[y])` where
    `y` is freshly chosen from `L₀ ∪ Γ.dom`. **The MSubRed sub-
    derivations of `hwfBody_old` are produced by `hB y hyL₀` (the
    cofinite WfM constructor), and they may legitimately contain
    `Ms-Pro y` steps**: the binding `⟨y, bound, .sub⟩` is in scope
    and `body^[y]` may contain `.fvar y`, which `WSubM.lf2`'s
    `hred` may chain through `Ms-Pro y`. Freshness of `y` outside
    `Γ.dom` does NOT preclude `Ms-Pro y` because the `y` binding is
    ADDED at the head before the WfM derivation is constructed.

  * `Pss/Mpss/Commutation.lean:Lemma_1_inline_fun_fun_residual`
    (line 381). Narrowing the head annotation `t → t'` of a renamed
    body MSubRed `h_at_z : MSubRed (⟨z, t, .sub⟩ :: Γ) [] (body₂^[z])
    (body₃^[z])` where `z` is freshly chosen. **Same issue: the
    renamed `h_at_z` is built via `MSubRed.rename_sub` from a body
    MSubRed `hb₂_to_b` produced by Lemma 1's recursive IH. `Ms-Pro
    y` steps in the source become `Ms-Pro z` steps in the renamed
    target (per `MSubRed.subst_yz_sub_head`'s `pro` arm,
    `Renaming.lean:855-908`), so `z`-freshness does NOT yield
    `msAvoidsPro h_at_z z = true`**. The Lemma 1 IH would need to
    output an MSubRed satisfying `msAvoidsPro` w.r.t. fresh
    binders — an output-side property requiring deep restructuring
    of all Lemma 1 cases.

  Both call sites have the same fundamental obstacle: an MSubRed
  derivation in context `⟨y, t, .sub⟩ :: Γ` may legitimately
  contain `Ms-Pro y` steps (looking up `t`); freshness of `y`
  outside `Γ.dom` is not sufficient to rule out `Ms-Pro y` because
  the binding for `y` is precisely what makes such a lookup
  possible.

  **Conclusion:** The wire-up cannot be performed locally with the
  freshness invariants currently available. The honest path requires
  *either* (i) propagating `msAvoidsPro` premises through
  `_N_motive_sub` (Narrowing.lean) AND `_S_motive_sub`
  (TypeSafety.lean) AND a Lemma 1 output invariant (Commutation.lean)
  — all three layers — *or* (ii) finding a structural/semantic
  invariant on `WfM`/`WSubMStar`-derived MSubReds that rules out
  Ms-Pro on freshly-named binders. Neither option fits inside
  Narrowing.lean alone.

  Phase B's aux theorem is RETAINED as the proof witness; the
  axiom is RETAINED as the load-bearing API.
* **Estimated complexity:** Multi-file restructure (~500-1000 lines
  across Narrowing/TypeSafety/Commutation, plus an output invariant
  on Lemma 1 in `Pss/Mpss/Commutation.lean`). Not a single-iteration
  task.
* **Foundational note:** Earlier discharge plans (path A "WSubM
  transitivity" and path B "WSubMStar end-to-end") are NOT viable
  per the analysis on lines 300-380 of `Narrowing.lean` — both
  require infrastructure downstream of this file. The avoidance-
  witness path is the active target but blocked per the wire-up
  audit above.

### 3. `Lemma_10_Inversion`

* **File:** `Pss/Mpss/WellFormed.lean`, line 618.
* **Paper:** Appendix Lemma 10 (full form).
* **Statement:** `WSubMStar Γ (.abs t u) (.abs t' u') → WEquM Γ t t'`.
* **Status:** Outstanding active. Hits Theorem 5. **Partial discharge
  shipped 2026-05-04**: the `_sub` direction of the proof is now PROVEN
  (`_Lemma_10_Inversion_sub_partial` in `WellFormed.lean`, axiom-free).
  The `_star` direction's `WSubMStar.trs` case is `WEquM.trans`, which
  is shown to be **isomorphic to the diamond/confluence property** of
  MEqRed and therefore cannot be discharged without re-introducing the
  `Lemma_2_*` β-residuals into Theorem 5's closure (see Strategy A
  audit in `WellFormed.lean` §7.4).
* **Discharge plan (REVISED 2026-05-04 after counterexample):** A long
  blocker analysis (file lines 564-617) identifies the precise
  obstruction: stripping the `WSubMStar` to `MSub` and inverting
  `Me-Fun`/`Ms-Fun` chains yields `MEqRedStar Γ [] t t_w` and
  `MEqRedStar Γ [] t' t_w`. Two helper lemmas (`Lemma A`, `Lemma B`)
  extend `WEquM` backwards along forward `MEqRedStar` chains.
  **Closing requires `WfM Γ t_w` to seed `WEquM Γ t_w t_w` (rfl).**
* **The previous discharge plan — `WfM`-preservation under `MEqRed`
  at empty stack — is FALSE in this calculus.** A Lean-checked
  counterexample lives in `Pss/Mpss/WfMPreservation.lean`
  (`Lemma_WfM_preservation_MEqRed_counterexample`):
  - `Γ = [⟨"x", .app .top .top, .equ⟩]`. `Prevalid Γ` holds (closed,
    LC), but `.app .top .top` is *not* `WfM Γ` (Lemma 11).
  - `WfM Γ (.fvar "x")` via `Wf-PrE` (only requires Prevalid+binding).
  - `MEqRed Γ [] (.fvar "x") (.app .top .top)` via `Me-Pro` plus
    reflexive app-congruence.
  - But `WfM Γ (.app .top .top)` is impossible.
* **Structural cause:** `MEqRed.pro` reads off an `≡`-binding's stored
  term, which `Prevalid` only checks for `fv ⊆ Γ.dom` and `LC`. The
  paper's `WfM` and the calculus's `Prevalid` are not aligned —
  `≡`-bindings can store terms that are not themselves `WfM`. Step's
  `Lemma_6_EvaluationPreservesWf` is provable because `Step` never
  consults the context; `MEqRed` does.
* **Strategy B audit (2026-05-04, contravariant `WSubMStar`-direct
  formulation).** A subsequent attempt reformulated the inversion to
  return `WSubMStar Γ t' t` (contravariant on bound annotations) instead
  of `WEquM Γ t t'`. The hypothesis was that the FREE `WSubMStar.trs`
  constructor would let chain composition bypass the confluence wall.
  Findings:
  - The single-WSubM contravariant inversion `_Lemma_10_contra_inv_sub`
    is fully provable (analogous to `_Lemma_10_Inversion_sub_partial` but
    returning `WSubM Γ t' t`).
  - Two chain helpers — `WSubMStar.extend_left_via_MEqRed_fwd` and
    `WSubMStar.extend_right_via_MEqRed_back` — are also provable
    axiom-free (lift the WSubM-level prepend/append helpers to chains
    via `WSubMStar.rec` with a transducer motive).
  - The lift to `WSubMStar` level still fails at `WSubMStar.trs`. The
    plan agent's proposed `WSubMStar.preserves_abs` lemma — **the
    foundational claim that `WSubMStar Γ (.abs ..) v → ∃ t' u',
    v = .abs t' u'`** — is **FALSE**.
  - Counterexample: take `Γ = [⟨"x", α, .equ⟩]` for some α reducing to
    (.abs ..). Then `WSubM.rgh` consumes `MEqRed Γ [] (.fvar x) α'` (via
    `Me-Pro`, which fires on equ-bound variables); combined with
    `WSubM.rfl` on (.abs ..), this yields `WSubM Γ (.abs ..) (.fvar x)`.
    Hence `WSubMStar Γ (.abs ..) (.fvar x)` is inhabited — chains can
    "detour" through equ-bound variables. Symmetrically, `(.fvar x) ≤*_wf
    (.abs ..)` is also inhabited via `Ws-Lf1 + Me-Pro`, so trs can have
    fvar midpoints.
  - The `WfM Γ U` constructors give five midpoint shapes: `top`,
    `varSub`, `varEqu`, `fun_`, `app`. Only `fun_` admits direct IH
    composition. `top` requires the analogue of Lemma 11 at WSubMStar
    level (currently only available through Theorem 3 → β-residuals).
    `varSub` should be uninhabited (`Me-Pro` requires equ-binding, not
    sub-binding) but proving this requires a custom lemma. `varEqu`
    requires recursion through the binder's α (not structurally
    smaller — needs well-founded recursion on a different measure).
    `app` is similar to `varEqu` (e.g., `Me-Bet` allows `(.app (.abs t' .body)) → opening _ body`).
  - The auxiliaries (`_Lemma_10_contra_inv_sub`,
    `WSubMStar.extend_left_via_MEqRed_fwd`,
    `WSubMStar.extend_right_via_MEqRed_back`) are SHIPPED to
    `WellFormed.lean` §7.5 as future-reusable infrastructure.
* **Strategy A audit (2026-05-04, this discharge attempt).** The
  most promising recovery — Strategy 4 from the prior list, "Bypass
  `WfM Γ t_w` via a Church-Rosser-style proof" — was attempted as
  *Strategy A* (direct induction on the `WSubMStar` derivation, with
  `WEquM` chain helpers `left_chain` / `right_chain_back` /
  `right_chain_fwd` / `WEquM.trans`). Findings:
  - The single-step (`_sub`) direction is fully provable; see
    `_Lemma_10_Inversion_sub_partial` in `WellFormed.lean`.
  - The `_star` direction via `WSubMStar.trs` requires `WEquM.trans`
    (composing two `WEquM`s through a joining annotation). Structurally,
    `WEquM Γ a b` is a zigzag `a → m ← b`, so composing two zigzags
    requires confluence at the joining midpoint — i.e. **the diamond
    property of MEqRed**, which is the source of the `Lemma_2_*`
    β-residuals.
  - The plan agent's proposed `WEquM.right_chain_fwd` (Helper 3,
    "symmetrize, prepend on LHS, symmetrize again") contains a
    directional error: after symmetrizing `WEquM Γ a b` to
    `WEquM Γ b a`, the chain `b → c` cannot be prepended on the LHS
    of the symmetrized WEquM via `left_chain` (which requires a chain
    *ending* at b, not starting from b).
  - The paper's own proof routes through `Theorem 3` (transitivity
    elimination), which uses `Lemma_2_DiamondMEqRed` and would
    re-introduce all 5 β-residuals into Theorem 5's closure — net
    regression (4 → ~8 axioms).
* **Recovery strategies (none realized):**
  1. Strengthen `Prevalid` to a `WfCtx` mutually inductive with `WfM`.
  2. Strengthen `Wf-PrE` to require `WfM Γ α`.
  3. Restrict the lemma to `pro`-preserving derivations.
  4. Discharge the β-residuals first (so the paper-route discharge is
     net-neutral). The β-residuals (axioms #6-#10) are themselves
     blocked on missing infrastructure — see those entries.
  5. Restrict call sites to provide `trs`-free WSubMStar derivations
     (then the `_sub` partial discharge applies directly). Requires
     auditing every `WSubMStar.trs` construction — non-local refactor.
* **Estimated complexity:** Strategy (1) is a deep refactor (every
  Prevalid construction site upgrades). Strategy (4) is the
  pragmatic next step: discharge the β-residuals, then the axiom
  becomes a wrapper over `Theorem_3 + _Lemma_10_Inversion_sub_partial`.
  Strategy (5) is a moderate refactor of call sites.

* **Iteration shipped 2026-05-04 (`4fe6b1b`, `e99fd8c`).** Two pieces
  of axiom-free infrastructure landed for future Strategy-5/Strategy-1
  use, with sharper blocker analyses:
  - `WSubMStarTrsFree` predicate (`WellFormed.lean §7.3d`) +
    `_Lemma_10_Inversion_trsFree` private theorem. **Strategy 5 wire-up
    audit**: 2 `WSubMStar.trs → WfM.app` feeders at
    `TypeSafety.lean:1007/1026` (Lemma_6's appL/appR arms). Each
    prepends a single Prop-17-derived `MEqRed` onto a pre-existing
    chain. Collapsing them to trs-free shape requires `WSubM`
    transitivity (Wall 2) — Strategy 5 walls cleanly into Wall 2.
  - `WfCtxEqu` predicate + `WfCtxEqu.lookup_equ` lemma
    (`WfMPreservation.lean §3-4`). The §2 counterexample is excluded
    by construction. **Conditional WfM-preservation under `MEqRed`**:
    the `pro/top/var/tAp` cases close cleanly via `lookup_equ`; the
    `app/bet` cases reduce to **`WSubMStar` preservation under
    `MEqRed`**, which IS Wall 2. **Net finding**: Wall 3
    (`WfM`-preservation) reduces to Wall 2 (`WSubM`-transitivity / 
    `WSubMStar`-preservation). The two walls are the same problem.
  
  **Implication**: a single mutual induction on the WfM/WSubM/WSubMStar
  block (which is already mutual — see `WellFormed.lean` line 42)
  could in principle close BOTH walls plus Lemma_10_Inversion
  simultaneously. The Me-Bet case is the genuine sticking point —
  it routes through Lemma_10 itself in standard subject-reduction
  proofs, creating apparent circularity. Whether the mutual induction
  closes that circularity is an open architectural question;
  preliminary analysis suggests the `.trs` case of WSubMStar (where
  the midpoint is non-`.abs`) is where the cycle actually breaks.

### 4. `Lemma_30_msPro_x_axiom`

* **File:** `Pss/Mpss/Substitution.lean`, line 885.
* **Paper:** Appendix Lemma 30 (Ms-Pro arm).
* **Statement:** Residual `Ms-Pro y = x` arm of Lemma 30 (substitution
  preserves `MSubRed`). Under the paper's "no promotion of `x`" side
  condition, this case is vacuous.
* **Status:** Outstanding active. Hits Theorem 5.
* **Discharge plan:** A leaf-level discharge has already been produced:
  `Lemma_30_msPro_x` (in `Pss/Mpss/AvoidsPro.lean`, line 611) is a
  theorem that takes an `msAvoidsPro h x = true` witness and discharges
  the residual via `False.elim`. The axiom remains because the SOLE
  caller `Pss.Mpss.TypeSafety._S_lf2` (in `Lemma_7_*`'s `WSubM.lf2` arm)
  invokes `Lemma_30_ReductionUnderSubst_Sub` without an avoidance
  witness, and the `WSubM.lf2` constructor does not carry such a side
  condition. Removing the axiom requires:
  1. Threading an `msAvoidsPro` premise through `Lemma_30_*_Sub`'s
     cofinite arms (needs an alpha-equivariance lemma for `msAvoidsPro`,
     since the body recursion samples `pickFresh L`); AND
  2. Threading the avoidance witness through `TypeSafety.lean`'s
     `_S_motive_sub` motive.
  See file lines 845-883 for the full breakdown.
* **Estimated complexity:** Medium (~150-250 lines, mostly in
  `TypeSafety.lean` plumbing + alpha-equivariance lemma for
  `msAvoidsPro`).
* **Alternative path REJECTED 2026-05-03 (SubstOk-bridge).** A second
  approach was investigated: extracting a `WSubMStar Γ₁out αout tout`
  from the call site (where it lives, since `_S_lf2` constructs
  `SubstOk` from a `WSubMStar`) and using it to derive the residual
  `MSubRed`. Findings (full notes in `Pss/Mpss/Substitution.lean`
  Status (2026-05-03) docstring above the axiom):
  1. `SubstOk` carries only `Term.LC s` and `fv s ⊆ Γ.dom`; no `WSubM`.
  2. Even WITH the bridge, the axiom asks for a SINGLE `MSubRed` step,
     while the bridge yields at best a `WSubMStar` chain. No `MSubRed`
     constructor absorbs an arbitrary chain.
  3. Re-architecting `_S_motive_sub` to return `WSubMStar` instead of
     `WSubM` runs into the documented `WSubM`-transitivity blocker
     (cf. `Pss/Mpss/WSubMTrans.lean` §3): the `rgh` case requires
     subject reduction along `MEqRed` on the LHS of `≤_wf`, which is
     exactly the obstruction shared with axioms #2 and #3.
  Hence the SubstOk-bridge collapses to the same WSubM-transitivity
  cluster that obstructs `Lemma_10_Inversion` and
  `Lemma_24_NarrowingMSubRed`. It is not an independent attack vector.

### 5. `Proposition_17_beta_axiom`

* **File:** `Pss/Mpss/OperationalSem.lean`, line 81.
* **Paper:** Proposition 17 (β arm).
* **Statement:** For prevalid extended context `Γ; s` and LC well-scoped
  `(λ ≤ bound. body) arg`,
  `MEqRed Γ s ((.abs bound body) arg) (Term.opening arg body)`.
* **Status:** Outstanding active. Hits Theorem 5.
* **Discharge plan:** `MEqRed.bet`'s body sub-derivation is at `Γ; s`
  WITHOUT the binder added (paper-faithful — see `MEQRED-BET-AUDIT.md`).
  This makes `MEqRed.refl` opaque on freshly-opened bodies whose stray
  fvar isn't in `Γ.dom`.

* **Path 1 (custom β-helper) — REJECTED 2026-05-03 (blocker analysis).**
  The naive recipe ("walk `LC body^[y]` and use `MEqRed.var` at fvars
  since `MEqRed.var` has no fv-scope check") does NOT close. The wall is
  `MEqRed.app`'s constructor signature:

  ```
  | app : MEqRed Γ (v :: s) u u' → MEqRed Γ [] v v' →
          MEqRed Γ s (.app u v) (.app u' v')
  ```

  The first sub-derivation requires `MEqRed Γ (v :: s) u u'`, whose
  leaves (e.g. `MEqRed.var hpv`) require `PrevalidExt Γ (v :: s)`,
  requiring `fv v ⊆ Γ.dom`. When `body` syntactically contains an
  `.app a b` with `b` containing `.bvar 0`, the opened operand
  `b^[y]` free-mentions `y ∉ Γ.dom`, and PrevalidExt fails.

  Concrete counterexample to the naive walk: `body = .app (.bvar 0)
  (.bvar 0)`. Then `body^[y] = .app (.fvar y) (.fvar y)`. To build
  `MEqRed Γ s body^[y] body^[y]` via `MEqRed.app hu hv` we need
  `hu : MEqRed Γ (.fvar y :: s) (.fvar y) (.fvar y)`. The leaf
  `MEqRed.var hpv'` needs `PrevalidExt Γ (.fvar y :: s)`, requiring
  `{y} ⊆ Γ.dom`. FALSE for fresh y.

  **Strip variant also rejected.** Building the body refl at the
  extended context `⟨y, .top, .sub⟩ :: Γ` succeeds (PrevalidExt
  satisfies `{y} ⊆ insert y Γ.dom`). But the strip step
  `MEqRed (⟨y, .top, .sub⟩ :: Γ) s u u' → MEqRed Γ s u u'` fails on
  the `MEqRed.app` arm of its own structural recursion: stripping y
  from the operator's sub-derivation `MEqRed (⟨y, .top, .sub⟩ :: Γ)
  (v :: s) u u'` requires `y ∉ fv v` to re-establish PrevalidExt at
  unextended Γ. But `v` may free-mention y (the very case where the
  extended-context construction was needed). Construct and strip hit
  the SAME `.app`-operand wall.

  Examined alternatives within Path 1:
  - `MEqRed.rename_*` functors don't strip — they rename the binding
    name and the stray fvar to a new fresh name; the binding stays.
  - No other `MEqRed` constructor produces `.app` shapes (Me-tAp only
    handles `.app .top u`; Me-Bet only handles `.app (.abs t u) v`).
  - No structural restriction on `body` (e.g. "no `.bvar 0` under
    `.app`-operand") is implied by `LC (.abs t body)`.

* **Path 2 (alpha-equivariance) — FORBIDDEN.** Per the discharge-
  campaign constraints, alpha-equivariance is the cluster-wide
  blocker for the β-residual axioms (#6, #7, #9, #10). Path 2 unblocks
  Proposition 17 for the same fundamental reason it would unblock the
  β-residuals, but is the same multi-day refactor.

* **Path 3 (refine `MEqRed.bet`'s body premise to extended ctx) —
  FORBIDDEN.** Per `MEQRED-BET-AUDIT.md`, the unextended-Γ body
  premise is paper-faithful and is REQUIRED for Lemma 1's
  commutativity proof (Case Me-Bet × Ms-App, p. 9:19–9:20 of paper).
  Adding the binding would break Lemma 1.

* **Path 4 (Type-LC + alpha-aware MEqRed) — VIABLE BUT MULTI-DAY.**
  Redesign `MEqRed.bet` / `.fun_` / `.fOp` constructors to take a
  Type-valued cofinite quantifier whose sample point is invariant
  under the rename functors. The body premise becomes structurally
  observable (no fv-scope check, no Classical.choice). With this in
  place, the body refl on `body^[y]` could be built by structural
  recursion on body's structure (NOT body^[y]'s LC), resolving the
  `.app`-operand stray issue at the constructor-level. Cross-codebase
  refactor on the same scale as the Type-LC refactor (commit
  `ad3ff08`). See `PLAN.md`'s discharge-campaign Option B.

* **Estimated complexity:** Path 4 only (multi-day cross-codebase
  refactor, ~500-1000 lines). Path 1 is rejected; Paths 2 and 3 are
  forbidden.

### 6. `Lemma_1_ctx_axiom` *(private to `Pss.Mpss.Commutation`)*

* **File:** `Pss/Mpss/Commutation.lean`, line 158.
* **Paper:** Lemma 1 (context-evolution lift, paper-implicit).
* **Statement:** Lift a same-context joining derivation
  `(MEqRed Γ₀ s₀ t₁ t₃, MSubRed Γ₀ s₀ t₂ t₃)` across two parallel
  `↣*` evolutions `Γ₀; s₀ ↣* Γ₁; s₁` and `Γ₀; s₀ ↣* Γ₂; s₂` to a
  joining at `(Γ₁; s₁), (Γ₂; s₂)`.
* **Status:** Outstanding active. Hits Theorem 3, 4 and Lemma 1.
* **Discharge plan:** Documented in file lines 120-154. The fundamental
  obstruction is that `Ct-Stk` and `Ct-Ann` (single-step extensions)
  shift either the stack head or a context annotation under an
  `MEqRed`/`MSubRed` step, requiring `.equ`-narrowing of
  `MSubRed`/`MEqRed` along an `MEqRed`-step on the bound term — itself
  confluence-shaped (recursive). Both consumers actually pass
  reflexive-or-near-reflexive chains:
  1. The headline `Lemma_1_StrongCommutativity_sameCtx` passes
     `(refl, refl)`;
  2. The internal `_core` App × App arm passes `(refl, .stk .refl hv₂)`
     (single Ct-Stk on the stack head).
  An honest discharge would either (a) re-engineer App × App to avoid
  the stack-shift (reduce `v, v₂` to a common reduct via Lemma 2 first,
  then join at the common stack), or (b) cycle-break by inlining
  WSubM-transitivity from `TransitivityElim`.
* **Estimated complexity:** Medium (300-500 lines for the App × App
  refactor and the `.equ`-narrowing chain).

### 7. `Lemma_1_inline_app_bet_residual` *(private to `Pss.Mpss.Commutation`)*

* **File:** `Pss/Mpss/Commutation.lean`, line 171.
* **Paper:** Lemma 1, Ms-App × Me-Bet case (p. 22 of appendix).
* **Statement:** Closes the Ms-App × Me-Bet diagram given operator IH and
  the Me-Bet's body cofinite-quantified premise.
* **Status:** Outstanding active. Hits Theorem 3, 4 and Lemma 1.
* **Discharge plan:** Term-size induction with the paper's "no Me-Pro
  on `x`" side condition (`avoidsPro` Bool function, in
  `Pss/Mpss/AvoidsPro.lean`). The same blocker as the Lemma-2
  β-residuals: closing the diagram requires consuming `avoidsPro h₁ x =
  true → avoidsPro h₂' x = true` through the construction, but
  `MEqRed.refl` is built via `Classical.choice` on `Nonempty`, hiding
  its constructor tree from `avoidsPro`. The current
  `avoidsPro_refl` axiom (in `AvoidsPro.lean`) is a candidate
  unblocker but has not been threaded yet.
* **Estimated complexity:** Medium (~300-500 lines if `avoidsPro_refl`
  is consumed; large if Type-LC refactor is the path).

### 8. `Lemma_2_DiamondMEqRed_ctx_axiom` *(private to `Pss.Mpss.Diamond`)*

* **File:** `Pss/Mpss/Diamond.lean`, line 220.
* **Paper:** Lemma 2 (context-evolution lift).
* **Statement:** Mirror of `Lemma_1_ctx_axiom` for the all-`MEqRed`
  diamond setting.
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1, 2.
* **Discharge plan:** Same as `Lemma_1_ctx_axiom`. Additionally: the
  `_core` App × App arm uses this axiom in a small way (lifting across a
  single Ct-Stk step `Γ; v::s ↣ Γ; v'::s`). A targeted refactor of
  App × App could eliminate that internal use, leaving only the
  external (caller-supplied refl) usage.
* **Estimated complexity:** Medium (same shape as `Lemma_1_ctx_axiom`).

* **Phase 4 blocker (2026-05-03 session):** Phase 3's
  `MEqRed.stack_head_replace` is shipped (in `Renaming.lean` §9.3)
  but cannot be plugged into the App×App arm without first discharging
  its `cofinDomFresh` and `cofinAvoidsProSelf` premises on the IH
  outputs `hu'_w`, `hu₂_w`. These premises are non-trivial:
  - `cofinAvoidsProSelf` at the `fOp` arm requires
    `avoidsPro (hbody (pickFresh L)) (pickFresh L) = true`. The body
    `body^[y₀]` lives at context `⟨y₀, α, .equ⟩ :: Γ`, so `Me-Pro y₀`
    steps in the body are LEGAL — `_core`'s output may include them.
    There is therefore NO general `cofin_normalize` recipe for arbitrary
    `MEqRed Γ s u u'` that produces a witness with cofinAvoidsProSelf =
    true: at the fOp arm we cannot strip Me-Pro on the binding name.
  - Refl-shape rescue fails: `_core`'s App×App output sub-derivations
    (`hu'_w` from `ihu hu₂`, `hv'_v₃` from `ihv hv₂`) are arbitrary
    IH outputs, NOT refl-shaped, so an `avoidsPro_refl`-style trivial
    discharge is unavailable.
  - The only viable path is Option A: thread cofin* output guarantees
    through `_core`'s motive plus every `_inline_*` lemma's signature
    (`_inline_pro_pro`, `_inline_app`, `_inline_bet`, `_inline_fun_fun`,
    `_inline_fOp_fOp`, `_inline_tAp`). Each output construction (App,
    Pro, refl, fOp via rename_equ_no_fv, etc.) needs a cofin proof.
    `MEqRed.refl`'s cofin = true requires widening `L` in its `abs`
    case to include `fv body` and constructing dedicated lemmas
    `cofinDomFresh_refl`, `cofinAvoidsProSelf_refl`. This is a
    multi-day cross-cutting refactor (>500 lines, multiple files).
  - The estimate for Phase 4 has therefore been revised: it is NOT a
    one-line "plug stack_head_replace into App×App" — it requires the
    motive-threading refactor described above as a prerequisite.

* **Recommended next attempt (Phase 4a + 4b):**
  - **Phase 4a — `cofin_refl` lemmas.** Prove `cofinDomFresh_refl` and
    `cofinAvoidsProSelf_refl` for `MEqRed.refl _ _ _` by structural
    recursion on `Term.LC` (mirroring the existing `avoidsPro_refl`
    proof). Requires widening the `L` used inside `MEqRed.refl`'s `abs`
    case (or proving it works at the existing `L ∪ Γ.dom`). Estimated
    ~100-150 lines in `AvoidsPro.lean`.
  - **Phase 4b — `_core` motive enrichment.** Add cofin* output
    guarantees to `Lemma_2_DiamondMEqRed_core`'s motive and to all six
    `_inline_*` lemma signatures. Each output construction needs a
    cofin* proof. The fOp_fOp arm (which uses `rename_equ_no_fv`) needs
    a `cofin*_rename_equ_no_fv` preservation lemma. Estimated ~400-600
    lines across `Diamond.lean`, plus ~50-100 lines of preservation
    lemmas in `Renaming.lean`.
  - **Phase 4c — discharge in App×App.** Once Phases 4a and 4b are in
    place, the App×App arm can replace `_ctx_axiom` with two
    `MEqRed.stack_head_replace` calls (one per leg, using `hv` /
    `hv₂` to swap the stack head). The premises are immediate from
    the enriched IH output guarantees.

* **Phase 4b reassessment (2026-05-03, second pass):** A second-pass
  analysis confirms Phase 4b as decomposed above runs into the same
  alpha-equivariance trap that Phase 1's §7.1 docstring (in
  `Renaming.lean`) and the false `avoidsPro_alpha_equiv` axiom (reverted
  in `12da200`) both warn against. **TWO independent blockers**:

  1. **cofin*-preservation lemmas for rename functors require
     alpha-equivariance.** All `MEqRed.rename_*` functors
     (`rename_stray`, `rename_sub`, `rename_equ_no_fv`, etc.) widen the
     cofinite L set by `{y, z}` at every `bet`/`fun_`/`fOp` arm: the
     output is `MEqRed.bet (L ∪ {y, z}) ...`, so its `cofinDomFresh`
     samples at `pickFresh (L ∪ {y, z})`, NOT `pickFresh L`. Proving
     `cofinDomFresh (rename_stray h y z hy hz) = cofinDomFresh h`
     (or even `... = true` from `cofinDomFresh h = true`) requires
     equating the body's cofin* values at TWO DIFFERENT canonical
     witnesses — exactly the FALSE alpha-equivariance statement. No
     constructive proof is available.

  2. **`_core`'s motive enrichment requires INPUT cofin* hypotheses
     that cannot be supplied at the public `Lemma_2_DiamondMEqRed`
     entry point.** The motive must look like:
     ```
     (h₂ : MEqRed Γ s t₀ t₂) →
     cofinDomFresh h₁ = true → cofinAvoidsProSelf h₁ = true →
     cofinDomFresh h₂ = true → cofinAvoidsProSelf h₂ = true →
     Σ' t₃ (h₁' ...) (h₂' ...), <output cofin* obligations>
     ```
     because the Pro × Var case OUTPUTS `MEqRed.pro hpv₂ heq₁ hα₁`
     where `hα₁` is the input's inner derivation, so output cofin*
     reduces (by `cofinDomFresh_pro` simp) to cofin* of the input's
     sub-derivation. Without input cofin* hypotheses, this case
     cannot discharge.

     But cofin* on arbitrary inputs is NOT constructable (per the
     2026-05-03 first-pass blocker analysis: cofin_normalize is
     impossible because `Me-Pro y₀` steps in fOp body bodies are
     legal). So `Lemma_2_DiamondMEqRed`'s public signature would have
     to ADD cofin* hypotheses on `h₁`, `h₂` — changing the public
     statement. This is unacceptable: Lemma 2's paper-faithful form
     does not include such side conditions, and the downstream
     consumers (notably `Theorem_3_TransitivityIsAdmissible` via
     `Lemma_1_StrongCommutativity`) would need to supply them, which
     they cannot.

  **What Phase 4b CAN ship without alpha-equivariance.** The refl-shape
  arms (where `_core` outputs `MEqRed.refl ...`) discharge cofin* via
  Phase 4a's `cofinDomFresh_refl` / `cofinAvoidsProSelf_refl`. The
  direct constructor outputs (`MEqRed.app`, `MEqRed.pro`,
  `MEqRed.bet`, etc.) distribute cofin* through their simp lemmas,
  but reduce to cofin* of sub-derivations — which requires either
  IH outputs (recursive, fine) OR input data (alpha-equivariance trap).

  The `_inline_fun_fun` / `_inline_fOp_fOp` arms produce outputs via
  `MEqRed.rename_sub` / `MEqRed.rename_equ_no_fv` — these introduce
  L widening and immediately hit blocker (1).

  **Verdict: Phase 4b as decomposed is NOT FEASIBLE.** A different
  strategy is required to remove `Lemma_2_DiamondMEqRed_ctx_axiom`
  from headline closures.

* **Alternative paths forward (none ready):**
  - **Type-LC + alpha-aware `MEqRed`.** Redesign `MEqRed.bet`/`.fun_`/
    `.fOp` constructors to take a body via Type-valued cofinite
    quantifier (rather than the current `∀ y, y ∉ L → ...`). The
    rename functors then produce derivations with the SAME L (sample
    point invariant). cofin* preservation becomes definitional.
    Cross-codebase refactor on the scale of the Type-LC refactor
    (commit `ad3ff08`).
  - **Side-condition-strengthened public Lemma 2.** Accept that public
    `Lemma_2_DiamondMEqRed` requires cofin* on inputs (paper-faithful
    forms exist that take auxiliary measure premises). All callers
    in `Lemma_1_StrongCommutativity`, `Theorem_3_TransitivityIsAdmissible`,
    etc. would need to supply them. Probably impossible without
    discharging cofin* at the call site, which is the same trap.
  - **Direct `_ctx_axiom` discharge via .equ-narrowing chain.** The
    original `_ctx_axiom` discharge plan from `AXIOMS.md` (the
    confluence-shaped recursive narrowing) is independent of the
    Phase 3/4 stack_head_replace approach. ~300-500 lines.
  - **Drop the App×App internal use of `_ctx_axiom`.** Restructure
    `_inline_app`'s App×App arm to NOT use `_ctx_axiom` — e.g.,
    by performing the `v ⟶ v'` swap before calling `ihu`, so the
    operator IH already lives at the right stack. Requires refactoring
    `_core`'s induction scheme to share `v` between App×App
    sub-derivations differently. Speculative; needs deeper analysis.

### 9. `Lemma_2_inline_app_bet_residual_axiom` *(private to `Pss.Mpss.Diamond`)*

* **File:** `Pss/Mpss/Diamond.lean`, line 292.
* **Paper:** Lemma 2, App × Bet diagonal (case grid).
* **Statement:** Closes `(MEqRed Γ (v::s) (.abs t' body') u', MEqRed Γ s ((.abs t' body') v) (opening v₂' body''))`
  given operator and operand IHs.
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1, 2.
* **Discharge plan:** Term-size induction bounded by `avoidsPro`. See
  the long discussion in `Diamond.lean` lines 93-150 ("moreover-clause
  threading blocker"). The blocker is `avoidsPro (MEqRed.refl _) x =
  true` not being structurally provable because `MEqRed.refl` extracts
  via `Classical.choice` from a `Nonempty`-wrapped derivation. Three
  paths discussed in the file:
  1. Type-valued `Term.LC` (cross-codebase refactor — see Option B in
     `PLAN.md`'s discharge-campaign section);
  2. Source-driven refl construction (~200 lines of mirror-recursion);
  3. Consume the existing `avoidsPro_refl` axiom (one-line, would
     unblock all three β-residuals).
* **Estimated complexity:** Medium on path 3 (~200-400 lines); medium
  on path 2 (~200 lines mirror); large on path 1 (cross-codebase).

### 10. `Lemma_2_inline_bet_residual_axiom` *(private to `Pss.Mpss.Diamond`)*

* **File:** `Pss/Mpss/Diamond.lean`, line 362.
* **Paper:** Lemma 2, Bet × {App, Bet} cases.
* **Statement:** Closes the diagram for sources of the form
  `.app (.abs t body) v` reduced by `Me-Bet` on the LHS.
* **Status:** Outstanding active. Hits Theorem 3, 4, 5 and Lemma 1, 2.
* **Discharge plan:** Same shape and same blocker as
  `Lemma_2_inline_app_bet_residual_axiom`.
* **Estimated complexity:** Same as #9.

---

## Inactive outstanding (no longer in any headline theorem's transitive deps)

Retained for documentation / paper-faithfulness / partial-discharge
reasoning. None of these are consumed by Theorem 3, 4, 5; Lemma 1, or
Lemma 2.

### 11. `Lemma_10_InversionRestricted`

* **File:** `Pss/Mpss/WellFormed.lean`, line 640.
* **Paper:** Appendix Lemma 10 (alternative formulation).
* **Statement:** `WSubMStar Γ (.abs t u) (.abs t' u') → ∃ z, MEqRedStar Γ [] t z ∧ MEqRedStar Γ [] t' z`.
  Returns a common `MEqRedStar` reduct rather than `WEquM Γ t t'`.
* **Status:** Inactive outstanding. Currently unused downstream (the
  Theorem-5 chain consumes `Lemma_10_Inversion` directly).
* **Discharge plan:** Provable WITHOUT `WfM`-preservation: stripping
  `WSubMStar` to `MSub` immediately yields the common reduct. Retained
  as documentation of the restricted variant.
* **Estimated complexity:** Small (~50-100 lines if anyone wants to
  prove it).

### 12. `avoidsPro_refl` — DISCHARGED (post Type-LC refactor)

* **File:** `Pss/Mpss/AvoidsPro.lean`, line 457.
* **Statement:** `avoidsPro (MEqRed.refl hpv hLC hfv) x = true` for any
  context, term, scope witness, and variable name.
* **Status:** PROVED as a theorem in commit `64162c2` (branch
  `type-lc-experiment`). With `Term.LC : Type` (post-Type-LC refactor),
  `MEqRed.refl` is built by direct structural recursion on the LC
  witness without `Classical.choice`, so the constructor tree of
  `MEqRed.refl` is observable to the `simp [MEqRed.refl, avoidsPro_*]`
  unfolding. The theorem mirrors the recursion of `MEqRed.refl` exactly.

---

## Lemmas the paper covers and we have proved

* **Lemma 15** (paper appendix): `Γ ⊢ u ≡_wf v ⟹ Γ ⊢ v ≡_wf u`.
  PROVED in `Pss/Mpss/WellFormed.lean` as `Lemma_15_WEquM_symm`.
* **Lemma 16** (paper appendix): `Γ ⊢ u ≡_wf v ⟹ Γ ⊢ u ≤_wf v`.
  PROVED in `Pss/Mpss/WellFormed.lean` as `Lemma_16_WEquM_to_WSubM`.
* **Proposition 18** (Reflexivity of `⟶^≡` and `⟶^≤`). PROVED in
  `Pss/Mpss/Diamond.lean` (`Proposition_18_*`), via `MEqRed.refl` /
  `MSubRed.refl` (the latter via `Ms-Equ`).
* **Lemma 7** (Substitution preserves `WfM`). PROVED in
  `Pss/Mpss/TypeSafety.lean` (`Lemma_7_SubstitutionPreservesWf`),
  including the generalized form. The paper's appeal to Conjecture 8
  in the Wf-App case is replaced by a direct IH on the `WSubMStar`
  premises — Conjecture 8 is therefore NOT in Theorem 5's closure.
* **Lemma 6** (Evaluation preserves `WfM`). PROVED in
  `Pss/Mpss/TypeSafety.lean` (`Lemma_6_EvaluationPreservesWf`),
  conditional on `Lemma_10_Inversion` and `Lemma_7_*`.
* **Lemma 11 (restricted)** (Top has no function supertype). PROVED in
  `Pss/Mpss/TypeSafety.lean` (`Lemma_11_TopHasNoFunctionSupertype`),
  via `WSubMStar.toMSub` + chain inversions.
* **`MEqRed.toScoped` / `MSubRed.toScoped`** (formerly Wave-4 axioms):
  PROVED in `Pss/Mpss/Weakening.lean` (lines 491/497).

## Audit

```
nix develop --command lake build Pss.Sanity
```

prints the full axiom dependency lists for each headline theorem (one
per `#print axioms` line). The expected baseline is `propext`,
`Quot.sound`, `Classical.choice` plus the paper-level axioms above.
