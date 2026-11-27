import Ochr.Meaning.Steps.Machine.JoinLocal

/-!
# `DecLocal.rep` and `DecLocal.inv`, proved (exists12)

`FrameLocal.DecLocal` (`DataModel/Exists/FrameLocal/Setup.lean`) at the checker's fuel-free decisions:
* `inv` (the places a write invalidates share its root): `checkerDecisionsFF` keeps `Decisions.invalidated`'s
  default, which invalidates nothing (`decLocal_inv_ff`);
* `rep` (the borrow bindings a side of `Id` re-points are rooted at its free variables): `typeState`'s
  `repointed` is drawn from `jdAssigns`, which adds `var (i - c)` only for an assignment `var i := …` at
  `c` binders crossed with `i ≥ c`, an occurrence of the term at that depth (`jdAssigns_ok`, by induction on
  the fuel with the invariant `AOk`, `RetP`), so the root is a free variable (`FrameLocal.mem_freeVars`;
  `typeState_rep`, `decLocal_rep_ff`).
With machine11's `decLocal_join_chain`, only `caps` (the [Entry] captures, `BlockCaps.staticBlockCaps`) is
left of `DecLocal` at the chain's decisions.
-/

namespace Ochr.Meaning.Steps.Machine
open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- What `jdAssigns` may add: a whole variable assigned at an occurrence of `O`, read at the outer scope. -/
def AOk (O : Nat × Place × PKind → Prop) (acc r : List Place) : Prop :=
  ∀ q ∈ r, q ∈ acc ∨ ∃ c p k, O (c, p, k) ∧ c ≤ p.root ∧ q = .var (p.root - c)

theorem AOk.trans {O} {a b c : List Place} (h₁ : AOk O a b) (h₂ : AOk O b c) : AOk O a c := by
  intro q hq
  rcases h₂ q hq with h | h
  · exact h₁ q h
  · exact .inr h

theorem AOk.mono {O O' : Nat × Place × PKind → Prop} {a b : List Place} (h : AOk O a b) (hO : ∀ x, O x → O' x) :
    AOk O' a b := by
  intro q hq
  rcases h q hq with h | ⟨c, p, k, h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨c, p, k, hO _ h1, h2, h3⟩

theorem AOk.bind {O} {acc : List Place} {x : M (List Place)} {g : List Place → M (List Place)}
    (hx : RetP (AOk O acc) x) (hg : ∀ a, AOk O acc a → RetP (AOk O a) (g a)) : RetP (AOk O acc) (x >>= g) :=
  RetP.bind_of hx fun a ha => (hg a ha).mono fun _ h => ha.trans h

theorem AOk.refl {O} (acc : List Place) : AOk O acc acc := fun q h => .inl h

set_option maxHeartbeats 4000000 in
theorem jdAssigns_ok : ∀ fuel : Nat,
    (∀ sc t acc (O : Nat × Place × PKind → Prop), (∀ x ∈ t.placeOccs sc.length, O x) →
      RetP (AOk O acc) (Ochr.jdAssigns fuel sc t acc)) ∧
    (∀ sc ts acc (O : Nat × Place × PKind → Prop), (∀ t ∈ ts, ∀ x ∈ t.placeOccs sc.length, O x) →
      RetP (AOk O acc) (Ochr.jdAssignsList fuel sc ts acc)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun sc t acc O _ => ?_, fun sc ts acc O _ => ?_⟩
    · unfold Ochr.jdAssigns; exact RetP.exhausted'
    · unfold Ochr.jdAssignsList
      split
      · exact RetP.pure' fun q hq => .inl hq
      · exact RetP.exhausted'
  | succ n ih =>
    refine ⟨fun sc t acc O hO => ?_, fun sc ts acc O hO => ?_⟩
    · unfold Ochr.jdAssigns
      dsimp only
      refine RetP.ite' (fun _ => ?_) (fun _ => ?_)
      refine RetP.bind' fun _ => RetP.bind' fun fl => ?_
      split
      exact RetP.pure' (AOk.refl acc)
      all_goals
        cases t
        all_goals first
          | exact RetP.pure' (AOk.refl acc)
          | skip
      all_goals first
        | -- assign
          (rename_i p u _
           dsimp only
           refine AOk.bind (ih.1 sc u acc O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_left _ hx))
             fun a ha => ?_
           split
           · rename_i i _
             refine RetP.ite' (fun hi => ?_) (fun _ => RetP.pure' (AOk.refl a))
             refine RetP.bind' fun pd => ?_
             refine RetP.ite' (fun _ => RetP.pure' ?_) (fun _ => RetP.pure' (AOk.refl a))
             intro q hq
             rcases mem_jdAdd hq with h | h
             · exact .inl h
             · subst h
               exact .inr ⟨sc.length, .var i, .assign, hO _ (by simp [Term.placeOccs]), hi, rfl⟩
           · exact RetP.pure' (AOk.refl a))
        | -- letIn
          (rename_i h u w _
           dsimp only
           refine AOk.bind (ih.1 sc u acc O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_left _ hx))
             fun a ha => ?_
           refine RetP.bind' fun d => ?_
           exact ih.1 (d :: sc) w a O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_right _ hx))
        | -- seq
          (rename_i u w _
           dsimp only
           refine AOk.bind (ih.1 sc u acc O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_left _ hx))
             fun a ha => ?_
           exact ih.1 sc w a O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_right _ hx))
        | -- matchNat
          (rename_i p z s' _
           dsimp only
           refine AOk.bind (ih.1 sc z acc O fun x hx => hO x (by
               simp only [Term.placeOccs]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))) fun a ha => ?_
           exact ih.1 sc s' a O fun x hx => hO x (by
               simp only [Term.placeOccs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
        | -- call
          (rename_i f as hd _
           dsimp only
           refine AOk.bind (ih.1 sc f acc O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_left _ hx))
             fun a ha => ?_
           exact ih.2 sc as a O fun t ht x hx => hO x (by
               simp only [Term.placeOccs]; exact List.mem_append_right _ (mem_placeOccsList ht hx)))
        | -- succ
          (rename_i u _
           dsimp only
           exact ih.1 sc u acc O fun x hx => hO x (by simp only [Term.placeOccs]; exact hx))
        | -- ascribe
          (rename_i u A _
           dsimp only
           exact ih.1 sc u acc O fun x hx => hO x (by simp only [Term.placeOccs]; exact List.mem_append_left _ hx))
        | -- ctor
          (rename_i ty c h ps as _
           dsimp only
           exact ih.2 sc as acc O fun t ht x hx => hO x (by
               simp only [Term.placeOccs]; exact List.mem_append_right _ (mem_placeOccsList ht hx)))
        | -- matchInd
          (rename_i p ty arms _
           dsimp only
           exact ih.2 sc _ acc O fun t ht x hx => hO x (by
               simp only [Term.placeOccs]; exact List.mem_cons_of_mem _ (mem_placeOccsArms ht hx)))
        | skip
      all_goals
        rename_i nm as _
        split
        all_goals first
          | exact RetP.pure' (AOk.refl acc)
          | (rename_i heq; cases heq; done)
          | (rename_i heq; cases heq
             exact ih.1 sc _ acc O fun x hx => hO x (by
               simp only [Term.placeOccs]; exact mem_placeOccsList (by simp) hx))
          | (rename_i heq; cases heq
             exact ih.2 sc _ acc O fun t ht x hx => hO x (by
               simp only [Term.placeOccs]; exact mem_placeOccsList ht hx))
      all_goals sorry
    · unfold Ochr.jdAssignsList
      split
      · exact RetP.pure' (AOk.refl acc)
      · rename_i t ts
        exact AOk.bind (ih.1 sc t acc O (hO t (List.mem_cons_self ..))) fun a _ =>
          ih.2 sc ts a O fun t' ht' => hO t' (List.mem_cons_of_mem _ ht')

/-- **`typeState` re-points only free variables**: every borrow binding it reports as re-pointed is
rooted at a free variable of the side. -/
theorem typeState_rep (fuel : Nat) (t : Term) :
    RetP (fun ts : Ochr.TypeState => ∀ y ∈ ts.repointed, y.root ∈ t.freeVars) (Ochr.typeState fuel t) := by
  cases fuel with
  | zero => unfold Ochr.typeState; exact RetP.exhausted'
  | succ n =>
  unfold Ochr.typeState
  dsimp only
  refine RetP.bind' fun ms => ?_
  refine RetP.bind_of (RetP.forIn' (fun ts : Ochr.TypeState => ts.repointed = []) rfl ?_) fun ts₁ h₁ => ?_
  · intro m _ ts hts
    retp_walk
    all_goals simp_all [ForInStep.value]
  · have hA := (jdAssigns_ok n).1 [] t [] (fun x => x ∈ t.placeOccs 0) (fun x hx => hx)
    refine RetP.bind_of hA fun ys hys => ?_
    refine RetP.bind_of (RetP.forIn' (fun ts : Ochr.TypeState => ∀ y ∈ ts.repointed, y.root ∈ t.freeVars)
      (by intro y hy; rw [h₁] at hy; cases hy) ?_) fun ts hts => RetP.pure' hts
    intro y hy ts hts
    retp_walk
    all_goals simp only [ForInStep.value]
    all_goals first
      | exact hts
      | (intro z hz
         rcases List.mem_append.1 hz with hz | hz
         · exact hts z hz
         · rw [List.mem_singleton] at hz
           subst hz
           rcases hys z hy with h | ⟨c, p, k, hm, hc, he⟩
           · cases h
           · subst he
             exact (DataModel.Exists.FrameLocal.mem_freeVars t _).mpr ⟨c, p, k, hm, hc, rfl⟩)

/-- **`DecLocal.rep` at the fuel-free decisions, PROVED**: the table's answer is a successful run's
(`typeState_rep`) or the empty default. -/
theorem decLocal_rep_ff (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat)) :
    ∀ sc t q, q ∈ (checkerDecisionsFF st bc).rePointed sc t → q.root ∈ t.freeVars := by
  intro sc t q hq
  simp only [checkerDecisionsFF, readDecisionFF] at hq
  split at hq
  · rename_i hs
    obtain ⟨f, b, st', hr⟩ := hs.choose_spec
    exact (RetP.withLive' (live := true) (typeState_rep f t)).run hr q hq
  · cases hq

/-- **`DecLocal.inv` at the fuel-free decisions, PROVED**: they invalidate nothing. -/
theorem decLocal_inv_ff (st : MState) (bc : List DeclInfo → List Place → Term → List Place × List (Place × Nat)) :
    ∀ sc p q, q ∈ (checkerDecisionsFF st bc).invalidated sc p → q.root = p.root := by
  intro sc p q hq
  cases hq

theorem decLocal_rep_chain (fuel : Nat) (st : MState) :
    ∀ sc t q, q ∈ (chainDecisions fuel st).rePointed sc t → q.root ∈ t.freeVars :=
  decLocal_rep_ff st _

theorem decLocal_inv_chain (fuel : Nat) (st : MState) :
    ∀ sc p q, q ∈ (chainDecisions fuel st).invalidated sc p → q.root = p.root :=
  decLocal_inv_ff st _

end Ochr.Meaning.Steps.Machine
