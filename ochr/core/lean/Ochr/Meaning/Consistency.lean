import Ochr.Meaning.Program
import Ochr.Meaning.Bounded
import Ochr.Meaning.Steps.Tail
import Ochr.Meaning.Steps.Knot

/-!
# Milestone 4: the assembly of `consistencyBounded` (docs/18 Corollaries 15 and 16)

The chain, each link a statement here; `consistencyBounded_assembled`, `consistency_rel`,
`defn_member` and `step_member` are assembled with no `sorry` in their bodies (docs/31 D72), from
the leaves below and the step lemmas (`Steps/*.lean`). Writing them found the knot of [Def]
(`step_member_fix`, `Regress/DefKnot.lean`):
1. **Acceptance resolves.** `Accepted (Prelude.decls ++ q) fuel` means every declaration resolves
   to an item (`Run.checkProgram`'s first loop) and `checkDefs` gives each item `accepted`; so
   the items are checked in order from the Σ of the earlier ones, exactly as `progMeaning`
   steps through them (`Program.progMeaning_sig`).
2. **Every accepted definition means an element of its type** (`defn_member`): by induction on
   the items, an accepted function's closure is a member of its Π-type (`Steps/Tail.checkFix_sound`)
   and an accepted constant's value a member of its goal (`checkConst_sound`), under the globals'
   meanings so far; the data model covers every accepted declaration (`checkInd_sound`).
3. **`False` means the empty proposition**: the library's `False` has no constructors, so its
   carrier is empty and `tyM` gives `prop False` (`false_means_empty`, a law of the data model
   for the library's declaration, which `libModel` and the generic model satisfy).
4. **Consistency**: a parameterless definition of type `False` would mean a member of `prop
   False`, that is, a proof of `False` (`Sem.mem proof (prop P) = P`); so there is none.
A data model exists for every accepted program (`exists_dataModel`, data-generic's generic
construction), which turns the relative statement into `consistencyBounded`.

What the assembly covers as the run stands (docs/31 D12): definitions whose Π-type is in `Type₀`
or `Prop`; polymorphic definitions wait on the level-1 construction.
-/

namespace Ochr.Meaning.Assembly

open Ochr.Meaning Ochr.Surface Ochr.Consistency

section
variable (dm : DataModel) (D : MState → Decisions)

/-- **The data model is faithful to the program** (a named hypothesis of the chain, docs/31 D72):
its field types, parameter types and recursive arguments are the declarations' as the run reads them.
As `exists_dataModel` stood, a model ignoring the program met it, and `fieldTypesOf_step` is false at
such a model (the data-model lane, `spine-datamodel`, docs/34); that lane is drafting the statement,
which replaces this placeholder and becomes a clause of `CtxOk`. -/
opaque DataFaithful (dm : DataModel) (P : ProgState) : Prop

/-- Every accepted definition so far means a member of its type. -/
def MeansMember (P : ProgState) : Prop := ∀ n s T, (n, s, T) ∈ P.means → s ∈ₛ[dm.read] T.m

/-- The item `it` is accepted from the Σ of `P` (`checkDefs`' verdict boundary). -/
def ItemAccepted (fuel : Nat) (P : ProgState) (it : Item) : Prop :=
  (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 matches .ok () _

/-- **A constant's check taken apart** (leaf): `checkDef`'s constant branch, the environment reset to
one empty frame, the goal evaluated, then the body evaluated typed at the goal, then [Return]
(`bodyReturns`), then the global stored at the goal. At the body's start the state is good and meets
the context's conditions under the program's context so far (Σ's globals are members: the chain's
induction, `hP`; the data model covering and faithful), and it is related to the empty state at its
counter (`Steps.Rel.start`: it holds no borrow), out of tail position. -/
theorem const_split (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms = [])
    (hP : MeansMember dm P) (hcov : ∀ d' ∈ st'.inds, dm.covers d') (hfaith : DataFaithful dm P)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ (f : Nat) (st₁ st₂ st₃ : MState) (b₁ b₂ : Nat) (goal v : Value) (T? : Option Value),
      Good dm (P.ctx dm D st').M (P.ctx dm D st').Γ (fun _ => .err) st₁ ∧ Steps.CtxOk (P.ctx dm D st') (fun _ => .err) st₁ ∧
      Steps.Rel (P.ctx dm D st') (fun _ => .err) noFuture id st₁ (emptyState st₁.nextLoan) ∧ st₁.tailNext = false ∧
      Steps.Runs (Ochr.eval f true d.body (some goal)) st₁ b₁ (v, T?) st₂ ∧
      Steps.Runs (Ochr.bodyReturns f s!"{d.name} is defined as it" v goal [] "") st₂ b₂ () st₃ ∧
      ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = goal := by
  sorry

/-- (leaf) A state good with a value in flight has a future typed for it (`TypedAssignment` gives
each live borrow's type a member to end at). -/
theorem typedFutureF_exists (K : RunCtx) (ρ : Assignment) (st : MState) (fl : Flight)
    (hg : GoodF K.dm K.M K.Γ ρ st fl) : ∃ ψ, TypedFutureF K.dm K.M K.Γ ρ st fl ψ := by
  sorry

/-- **The constant's meaning is the checker's value's** (leaf): the reference's run of the body from
the empty state at the counter `0` and the constant future (`defMeaning`) is the run the step lemma
compared (from the empty state at the checker's counter, `FrameProp.run_counter_indep`; under the
extended assignment, which the closed body does not read, `run_abs_congr`; at a future the value
does not read once [Return] ended its borrows), at the goal (`hintM` is `globalTyS` at the stored
type), and at a proposition it is `•` (`constMean`): so the membership [Return] gives is the
definition's. -/
theorem const_value (fuel : Nat) (P : ProgState) (d : Def) (st' st₁ : MState) (goal v : Value) (hd : d.doms = [])
    (hgoal : ((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot = goal)
    (ρ' : Assignment) (Δ' : Nat → TyS) (D' : Decisions) (π' : Nat → Nat) (r : Res) (s₂ : SState)
    (hrun : runT (P.ctx dm D st') ρ' noFuture false (Steps.hintM (P.ctx dm D st') (fun _ => .err) (some goal)) d.body
      (emptyState st₁.nextLoan) = some (r, s₂))
    (hmean : meanV { P.ctx dm D st' with Δ := Δ', D := D' } ρ' (fun l => noFuture (π' l)) r.2 v = r.1) (ψ : Future)
    (hmem : meanV { P.ctx dm D st' with Δ := Δ', D := D' } ρ' ψ (Value.tyS dm ({ P.ctx dm D st' with Δ := Δ', D := D' } : RunCtx).M
        (P.ctx dm D st').Γ ρ' goal) v ∈ₛ[dm.read]
      (meanV { P.ctx dm D st' with Δ := Δ', D := D' } ρ' noFuture (.plain .err) goal).asTy) :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D st') d goal = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  sorry

/-- **An accepted constant means a member of its type** (assembled): the check taken apart
(`const_split`), the body by the step lemma (`eval_step`, from the start related to the empty state),
[Return]'s membership (`bodyReturns_sound`, in the extended context, the value in flight), the
constant's meaning that value's (`const_value`). -/
theorem step_member_const (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms = [])
    (hP : MeansMember dm P) (hcov : ∀ d' ∈ st'.inds, dm.covers d') (hfaith : DataFaithful dm P)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  obtain ⟨f, st₁, st₂, st₃, b₁, b₂, goal, v, T?, hg₁, hctx₁, hs₁, htl, hev, hbr, hgoal⟩ :=
    const_split dm D fuel P d st' hd hP hcov hfaith hrun
  obtain ⟨ρ', Δ', D', π', -, -, -, -, -, r, s₂, hrunr, hmean, -, hctx₂, -, hg₂⟩ :=
    (Steps.stepsIH f (P.ctx dm D st') (fun _ => .err) noFuture).eval_step st₁ st₂ true d.body (some goal) v T? hg₁
      hctx₁ _ id hs₁ (fun h => absurd h (by decide)) b₁ hev
  rw [htl] at hrunr
  obtain ⟨ψ, hψ⟩ := typedFutureF_exists { P.ctx dm D st' with Δ := Δ', D := D' } ρ' _ _ hg₂
  have hmem := ((Steps.stepsIH f { P.ctx dm D st' with Δ := Δ', D := D' } ρ' ψ).bodyReturns_sound st₂ st₃ _ v goal [] ""
    (Steps.flightOf r.2) hg₂ hctx₂ b₂ hbr hψ).1
  rw [hgoal]
  exact const_value dm D fuel P d st' st₁ goal v hd hgoal ρ' Δ' D' π' r s₂ hrunr hmean ψ hmem

/-- **An accepted function means a member of its type** (leaf; THE KNOT, docs/31 D72). Not
`checkFix_sound`: `checkDef` pushes the function's global before `checkFix`, so `CtxOk` at the state
`checkFix_sound` starts from already asks the function to be a member of its type
(`Regress/DefKnot.ctx_contains_fix_member`), and the statement is vacuous at a definition. What proves
it: the guarded recursion on the decreasing argument, by induction on its rank, the body's generic
run (`generic_good`, `Rel.start`, `checkTail_step`, the return check by `conv_sound` and
`bodyReturns_sound`) under a context asking of the function only membership at arguments of smaller
rank (the stage before, `RunCongr.fixStage`). That form of `GlobalsOk` for the definition being
checked is not stated. -/
theorem step_member_fix (fuel : Nat) (P : ProgState) (d : Def) (st' : MState) (hd : d.doms ≠ [])
    (hP : MeansMember dm P) (hcov : ∀ d' ∈ st'.inds, dm.covers d') (hfaith : DataFaithful dm P)
    (hrun : (runMachine (checkItem (.defn d)) { globals := P.globals, inds := P.inds } fuel).1 = .ok () st') :
    ∃ m, defMeaning (fun _ => .err) (P.ctx dm D st') d
        (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
  sorry

/-- **One item keeps every definition a member** (assembled): an inductive declaration adds no
definition; a definition's meaning is a member by `step_member_const` or `step_member_fix`. -/
theorem step_member (fuel : Nat) (P : ProgState) (it : Item) (hP : MeansMember dm P)
    (hacc : ItemAccepted fuel P it)
    (hcov : ∀ d' ∈ (ProgState.step dm D (fun _ => .err) {} fuel P it).inds, dm.covers d')
    (hfaith : DataFaithful dm P) :
    MeansMember dm (ProgState.step dm D (fun _ => .err) {} fuel P it) := by
  unfold ItemAccepted at hacc
  rcases hr : (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 with ⟨u, st'⟩ | f | e
  · cases u
    intro n s T hmem
    simp only [ProgState.step, hr] at hmem hcov
    cases it with
    | ind d' => exact hP n s T hmem
    | defn d =>
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · exact hP n s T hmem
      · have hm : ∃ m, defMeaning (fun _ => .err) (P.ctx dm D st') d
            (((st'.globals.find? (·.name == d.name)).map (·.ty)).getD .bot) = some m ∧ m.1 ∈ₛ[dm.read] m.2.m := by
          by_cases hd : d.doms = []
          · exact step_member_const dm D fuel P d st' hd hP hcov hfaith hr
          · exact step_member_fix dm D fuel P d st' hd hP hcov hfaith hr
        obtain ⟨m, hdm, hmm⟩ := hm
        rw [hdm] at hmem
        simp only [Option.getD_some, Prod.mk.injEq] at hmem
        obtain ⟨-, rfl, rfl⟩ := hmem
        exact hmm
  · rw [hr] at hacc; simp at hacc
  · rw [hr] at hacc; simp at hacc

/-- The items of a surface program, when every declaration resolves (`Run.checkProgram`'s first
loop, `runResolve`), in order. -/
def ResolvesTo (p : Program) (fuel : Nat) (items : List Item) : Prop :=
  items.length = p.length ∧
  ∀ (i : Nat) (d : SDecl) (it : Item), p[i]? = some d → items[i]? = some it →
    ∃ st, (runResolve p d fuel false).1 = .ok (.ok it) ∧ (runResolve p d fuel false).2 = st

/-- (1) An accepted program resolves to items each of which `checkDefs` accepts; and the state
each item is checked from is the Σ of the items before it. -/
theorem accepted_resolves (p : Program) (fuel : Nat) (acc : Accepted p fuel) :
    ∃ items, ResolvesTo p fuel items ∧
      ∀ (i : Nat) (it : Item), items[i]? = some it →
        let P := progMeaning dm D (fun _ => .err) {} fuel (items.take i)
        (runMachine (checkItem it) { globals := P.globals, inds := P.inds } fuel).1 matches .ok () _ := by
  sorry

/-- (leaf, checker) Along accepted items Σ's inductive declarations only grow (a definition adds
none, a declaration adds itself: `checkDef`, `checkInd`), so a data model covering the whole program
covers every prefix. -/
theorem covered_prefix (items : List Item) (fuel : Nat)
    (hacc : ∀ (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D (fun _ => .err) {} fuel (items.take i)) it)
    (hcov : (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm) :
    ∀ k, k ≤ items.length → (progMeaning dm D (fun _ => .err) {} fuel (items.take k)).Covered dm := by
  sorry

/-- (2) Every accepted definition's meaning is a member of its type, at the empty assignment
(assembled): by induction on the items, one item at a time (`step_member`), the data model
covering and faithful at each prefix. -/
theorem defn_member (items : List Item) (fuel : Nat)
    (hacc : ∀ (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D (fun _ => .err) {} fuel (items.take i)) it)
    (hcov : ∀ k, k ≤ items.length → (progMeaning dm D (fun _ => .err) {} fuel (items.take k)).Covered dm)
    (hfaith : ∀ k, k ≤ items.length → DataFaithful dm (progMeaning dm D (fun _ => .err) {} fuel (items.take k))) :
    MeansMember dm (progMeaning dm D (fun _ => .err) {} fuel items) := by
  have key : ∀ k, k ≤ items.length → MeansMember dm (progMeaning dm D (fun _ => .err) {} fuel (items.take k)) := by
    intro k
    induction k with
    | zero => intro _ n s T h; simp [progMeaning, progMeaningFrom] at h
    | succ k ih =>
      intro hk
      have hk' : k < items.length := hk
      have htake : items.take (k + 1) = items.take k ++ [items[k]] := List.take_succ_eq_append_getElem hk'
      have hfold : progMeaning dm D (fun _ => .err) {} fuel (items.take k ++ [items[k]]) =
          ProgState.step dm D (fun _ => .err) {} fuel (progMeaning dm D (fun _ => .err) {} fuel (items.take k)) items[k] := by
        unfold progMeaning progMeaningFrom; rw [List.foldl_append]; rfl
      have hc := hcov (k + 1) hk
      rw [htake, hfold] at hc ⊢
      exact step_member dm D fuel _ _ (ih (Nat.le_of_lt hk')) (hacc k items[k] (List.getElem?_eq_getElem hk')) hc
        (hfaith k (Nat.le_of_lt hk'))
  have := key items.length (Nat.le_refl _)
  rwa [List.take_length] at this

/-- (3) The library's `False` means the empty proposition: `tyM` of a declaration with no
constructors is `prop (Nonempty car)`, and a carrier with no constructor is empty
(`DataModel.pack_fields`: every element is a constructor applied to fields). -/
theorem false_means_empty (d : IndDecl) (hd : d.name = "False" ∧ d.ctors = [] ∧ d.sort = 0)
    (hcov : dm.covers d) : dm.tyM d [] = .prop False := by
  sorry

/-- The stored type of a parameterless definition declared `: False` is the library's `False`
applied to nothing, once the library is in front (names are distinct: `Check.declared`). -/
theorem falseConst_ty (q : Program) (fuel : Nat) (items : List Item) (d : SDecl)
    (hres : ResolvesTo (Prelude.decls ++ q) fuel items) (hd : d ∈ q) (hf : d.IsFalseConst) :
    let P := progMeaning dm D (fun _ => .err) {} fuel items
    ∃ s T, (d.name, s, T) ∈ P.means ∧ T.m = .prop False := by
  sorry

/-- (4) Consistency, relative to a data model covering the program, faithful to it, and the decisions
read from the checker (assembled): no accepted, hole-free, level-bounded program has a parameterless
definition of type `False`. Its meaning would be a member of `prop False`, a proof of `False`. -/
theorem consistency_rel (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel)
    (hcov : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm)
    (hfaith : ∀ items, ResolvesTo (Prelude.decls ++ q) fuel items →
      ∀ k, k ≤ items.length → DataFaithful dm (progMeaning dm D (fun _ => .err) {} fuel (items.take k))) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  intro d hd hf
  obtain ⟨items, hres, hacc⟩ := accepted_resolves dm D (Prelude.decls ++ q) fuel acc
  have hacc' : ∀ (i : Nat) (it : Item), items[i]? = some it →
      ItemAccepted fuel (progMeaning dm D (fun _ => .err) {} fuel (items.take i)) it := hacc
  have hmem := defn_member dm D items fuel hacc' (covered_prefix dm D items fuel hacc' (hcov items hres))
    (hfaith items hres)
  obtain ⟨s, T, hin, hT⟩ := falseConst_ty dm D q fuel items d hres hd hf
  have h := hmem _ s T hin
  rw [hT] at h
  obtain ⟨⟨a⟩, -⟩ := h
  exact a

end

/-- A data model covering every accepted program exists (the generic construction by stages,
`DataGeneric.lean`, data-generic), with the checker's decisions (`DecisionsInst.checkerDecisions`).
Since docs/31 D61 a data model also carries its reading (`DataModel.read`, `read_eq`): a field
holds a full meaning, a data field's read through the model's own reading, so the generic model
needs a reading coherent with it (`DataGeneric.Coherent`), a fixed point of model and reading not
yet constructed. The reading also gives whole fields (`DataRead.WholeFields`, docs/31 D68), so
that the record a borrow-returning call makes, the encoding of its forward value, is whole. -/
theorem exists_dataModel (items : List Item) (fuel : Nat) :
    ∃ (dm : DataModel) (D : MState → Decisions),
      (progMeaning dm D (fun _ => .err) {} fuel items).Covered dm ∧ dm.read.WholeFields ∧
      ∀ k, k ≤ items.length → DataFaithful dm (progMeaning dm D (fun _ => .err) {} fuel (items.take k)) := by
  sorry

/-- (leaf, checker) An accepted program resolves: `checkProgram`'s first loop gives every
declaration an item. -/
theorem resolves_of_accepted (p : Program) (fuel : Nat) (acc : Accepted p fuel) :
    ∃ items, ResolvesTo p fuel items := by
  sorry

/-- (leaf, checker) Resolution is a function of the program: two resolutions are the same items. -/
theorem resolvesTo_unique (p : Program) (fuel : Nat) (items items' : List Item)
    (h : ResolvesTo p fuel items) (h' : ResolvesTo p fuel items') : items = items' := by
  sorry

/-- `consistencyBounded` from the relative statement and the existence of a data model. -/
theorem consistencyBounded_assembled (q : Program) (fuel : Nat)
    (holes : NoHoles q) (levels : LevelsBelow 2 q)
    (acc : Accepted (Prelude.decls ++ q) fuel) :
    ∀ d ∈ q, ¬ d.IsFalseConst := by
  obtain ⟨items, hres⟩ := resolves_of_accepted (Prelude.decls ++ q) fuel acc
  obtain ⟨dm, D, hcov, -, hfaith⟩ := exists_dataModel items fuel
  refine consistency_rel dm D q fuel holes levels acc (fun items' h' => ?_) (fun items' h' => ?_)
  · rw [resolvesTo_unique _ _ _ _ h' hres]; exact hcov
  · rw [resolvesTo_unique _ _ _ _ h' hres]; exact hfaith

end Ochr.Meaning.Assembly
