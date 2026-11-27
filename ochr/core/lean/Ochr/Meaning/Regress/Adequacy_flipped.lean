import Ochr.Meaning.Attack.RunEqs
import Ochr.Meaning.Regress.CE4_flipped

/-!
# D19's batch, flipped: positive checks for the fixed reference run (built)

`Regress/Adequacy_1d94e4eb.lean` (unbuilt) records the run of 1d94e4eb failing on `f(f(a))` and on
`(let y = x; ()); x`. With D19's fixes:

* `head_in_place`: a call's head, when it is a place, is read in place: the value comes back and
  the state is as it was, whatever the place's declared reading (R2). So the inner call of
  `f(f(a))` finds `f` where the outer one read it.
* `stmt_keeps`: a term the decisions classify as a statement (`Decisions.flags`) leaves the state
  as it was and returns no label, whatever it reads or writes (R1), for the sequencing forms, a
  place, an assignment and a call. So `x` is still there after `let h : True = (let y = x; refl)`.

Axioms: propext, Classical.choice, Quot.sound.
-/

namespace Ochr.Meaning.Regress.AdequacyFlip
open Ochr Ochr.Meaning Ochr.Meaning.Attack Ochr.Meaning.Regress.CE4flip

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- One frame holding one binding, no holder. -/
def one (b : SBinding) (k : Nat) : SState := { env := [{ binds := [b] }], shape := fun _ => none, nextLoan := k }

/-- R2: the head of a call, a place, is read in place. -/
theorem head_in_place (b : SBinding) (k : Nat) (rn : SM Res) (hw : (b.val φ).whole)
    (hg : ReadGood K.dm.read b.ty.m (b.val φ)) :
    SM.headOf (.place (.var 0)) (fun p => SM.guarded (ContentOk K φ p) (readPlace K φ p true)) rn (one b k)
      = some ((b.val φ, { b.ty with label := none }), one b k) := by
  show SM.guarded (ContentOk K φ (.var 0)) (readPlace K φ (.var 0) true) (one b k) = _
  have hok : ContentOk K φ (.var 0) (one b k) := by
    have hr : resolve (one b k) (.var 0) = some (.bind 0 0, []) := by
      simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, one]
    unfold ContentOk; rw [hr]
    exact accessOk_noLive K φ (liveLabels_noshape _ rfl) _ _
  rw [SM.guarded_of hok]
  rw [readPlace_of φ K (.var 0) true (one b k) _ _ _ _ _ (contentOf_var0_one K φ k b)]
  simp [hw, hg, one]

/-- A statement or erased clause leaves the state as it was and returns no label. -/
theorem erasedIf_keeps {fl : Bool × Bool} {x : SM Res} {s s' : SState} {r : Res} (hfl : fl.1 = true)
    (h : SM.erasedIf fl x s = some (r, s')) : s' = s ∧ r.2.label = none := by
  by_cases he : fl.2 = true
  · obtain ⟨rfl, rfl⟩ := SM.erasedIf_erased he h
    exact ⟨rfl, rfl⟩
  · simp only [SM.erasedIf, he, Bool.false_eq_true, if_false] at h
    obtain ⟨hb, -⟩ | ⟨-, e, hl, -⟩ := SM.stmtIf_some h
    · rw [hfl] at hb; cases hb
    · exact ⟨e, hl⟩

/-- R1: a statement leaves the state as it was. -/
theorem stmt_keeps (t : Term) (hint : TyS) (s : SState) (hfl : (K.D.flags (scopeOf s) t).1 = true)
    (r : Res) (s' : SState) (h : run K ρ φ hint t s = some (r, s'))
    (ht : t matches .letIn .. | .seq .. | .matchNat .. | .matchInd .. | .assign .. | .place .. | .call ..) :
    s' = s ∧ r.2.label = none := by
  cases t <;> simp at ht <;>
    (rw [run, runT] at h; exact erasedIf_keeps hfl h)

/-- The audit's A3 and A17 under the strict run (C1, D83): an erased term (`Machine.evalAt`'s second
flag: a proof), a place included, runs on a copy of the state; where it runs to `•` its result is
`•` at `True` and the state is as it was. (Before the strict run an erased term was `•` unrun, at
`err`, and an erased place at its stored type; so a match on a proof with two arms, or none, which
fails when run, did not fail erased. It fails now: `erased_match_proof_fails`.) -/
theorem erased_on_copy (t : Term) (hint : TyS) (s : SState) (hfl : (K.D.flags (scopeOf s) t).2 = true)
    (ht : t matches .letIn .. | .seq .. | .matchNat .. | .matchInd .. | .assign .. | .call .. | .ctor .. | .fix .. | .place ..)
    (r : Res) (s' : SState) (h : run K ρ φ hint t s = some (r, s')) :
    s' = s ∧ r = (.proof, .plain (TyM.prop True)) := by
  cases t <;> simp at ht <;> (rw [run, runT] at h; exact SM.erasedIf_erased hfl h)

/-- **What was wrong, and what is left of it** (the lead's ruling 3, 2026-11-21). At a24fc76f the
strict run failed EVERY erased match on a proof with other than one arm: its clause found the tag
`•` and no arm to take (a proof scrutinee was matched by its type, D45, only where its proposition
has one constructor). The checker accepts such matches whose result is a proof:
`Subsingletons.OrComm`, `OrElim`, `OrLet` (two arms on `Or`) and `Propositions.absurdP` (no arms on
`False`) in `Examples/Propositions.lean`, so on `Or` the run failed where the checker succeeds, at
members. Then the arms ran, each on a copy (`SM.anyArm`), and the match failed only where no arm
ran to a proof: as with no arms (an empty proposition: no member to run at), or every arm failing. Since docs/31 D229
(the fourth referee's F2) a match on a proof of a declaration that is NOT a subsingleton (`Or`) runs no arm at all, as
the checker's untyped run does not (`erased_match_proof_runs`); the arms run on copies only at a subsingleton with
other than one arm, that is with none. -/
theorem erased_match_proof_fails (p : Place) (n : String) (arms : List (Hint × Term)) (hint : TyS) (tl : Bool)
    (s s₁ : SState) (hfl : (K.D.flags (scopeOf s) (.matchInd p n arms)).2 = true) (hsub : K.D.subsingleton n = true)
    (htag : tagOf K φ p indTag s = some (.proof, s₁)) (harms : arms.length ≠ 1)
    (hno : ∀ c, SM.ranProof (runArm K ρ φ tl (tailHint tl hint) c arms s₁) = false) :
    runT K ρ φ tl hint (.matchInd p n arms) s = none := by
  rw [runT]
  by_cases hT : ¬ TagOk K φ p s
  · simp [SM.erasedIf, hfl, bind, Option.bind, SM.guarded, hT]
  have hT : TagOk K φ p s := Classical.byContradiction hT
  simp only [SM.erasedIf, hfl, if_true, bind, Option.bind, SM.guarded_of hT, htag, matchEntry, Sem.isProof, Bool.not_true,
    Bool.and_false, Bool.false_and, if_false, harms, and_false, hsub, optCheck, MatchEntryOk]
  have hf : List.find? (fun _ => false) (List.range arms.length) = none := by
    rw [List.find?_eq_none]; intro _ _; exact Bool.false_ne_true
  simp [SM.anyArm, hno, hf]

/-- **`OrComm`'s shape runs** (ruling 3): an erased match on a proof with two arms, the first failing
(its constructor's field proposition false, say) and the second running to a proof, runs: `•` at
`True`, the state as it was. Since docs/31 D229 it runs without running either arm (`Or` is not a subsingleton:
`hsub`), so the arms' runs `h1`, `h2` are not read. -/
theorem erased_match_proof_runs (p : Place) (n : String) (h₁ h₂ : Hint) (t₁ t₂ : Term) (hint : TyS) (tl : Bool)
    (s s₁ s₂ : SState) (R : TyS) (hfl : (K.D.flags (scopeOf s) (.matchInd p n [(h₁, t₁), (h₂, t₂)])).2 = true)
    (hsub : K.D.subsingleton n = false)
    (hT : TagOk K φ p s) (htag : tagOf K φ p indTag s = some (.proof, s₁))
    (h1 : runT K ρ φ tl (tailHint tl hint) t₁ s₁ = none) (h2 : runT K ρ φ tl (tailHint tl hint) t₂ s₁ = some ((.proof, R), s₂)) :
    runT K ρ φ tl hint (.matchInd p n [(h₁, t₁), (h₂, t₂)]) s = some ((.proof, .plain (TyM.prop True)), s) := by
  rw [runT]
  simp only [SM.erasedIf, hfl, if_true, bind, Option.bind, SM.guarded_of hT, htag, matchEntry, Sem.isProof, Bool.not_true,
    Bool.and_false, Bool.false_and, if_false, optCheck, MatchEntryOk]
  simp [hsub]

/-- The audit's A9: a field of type `A` (the one parameter) given a `Nat` solves `A := Nat`
(`Pair(a, b)`, `Cons(x, xs)`'s head). -/
example : unifyTyS K.dm 1 (.place (.var 0)) (.plain TyM.nat) [none] = [some (.ty TyM.nat)] := rfl

/-- A9: a field of type `List(A)` given a value whose type is `List(Nat)`'s code (its declaration
and its record, which keeps `A`'s entry at `paramKey 0`) solves `A := Nat`. -/
example (A : Type) : unifyTyS K.dm 1 (.tind "List" [.place (.var 0)])
    (.plain (.t0 A (.data { name := "List" } (fun _ => .leaf Nat .nat) A))) [none]
    = [some (.ty TyM.nat)] := by
  simp [unifyTyS, fillParam, TyS.data, TyM.dataRec?, TyM.isErr, DataModel.paramTyOf]
  rfl

/-- A9: a solved parameter is not overwritten, and a field with no type (`err`) solves nothing. -/
example : unifyTyS K.dm 1 (.place (.var 0)) (.plain TyM.nat) [some (.ty TyM.unit)] = [some (.ty TyM.unit)] := rfl
example : unifyTyS K.dm 1 (.place (.var 0)) (.plain .err) [none] = [none] := rfl

/-- A9: the constructor clause with every parameter solved by its fields does not fail for want
of a hint: at no hint, no record is known before the fields, `sol₀` is all unsolved, and the
clause's result is decided by `runFields`' solution alone. -/
theorem ctor_no_hint (ty : String) (c : Nat) (x : Hint) (args : List Term) (s : SState) (d : IndDecl)
    (hd : K.Γ.find? (·.name == ty) = some d) (hfl : K.D.flags (scopeOf s) (.ctor ty c x [] args) = (false, false))
    (hp : d.params.isEmpty = false)
    (fs : List Sem) (sol : List (Option Sem)) (s' : SState)
    (hf : runFields K ρ φ (d.sort == 0) d c 0 none (List.replicate d.params.length none) [] args s = some ((fs, sol), s'))
    (hsol : sol.all (·.isSome) = true) (hs : (d.sort == 0) = false)
    -- STRICT: the value built is a member of its type
    (hm : K.dm.ctorM d (solved sol) c fs ∈ₛ[K.dm.read] K.dm.tyM d (solved sol)) :
    run K ρ φ (.plain .err) (.ctor ty c x [] args) s
      = some ((K.dm.ctorM d (solved sol) c fs, .plain (K.dm.tyM d (solved sol))), s') := by
  rw [run, runT]
  simp only [SM.erasedIf, hfl, SM.stmtIf, Bool.false_eq_true, if_false, hd, runParams, bind, pure, TyS.plain,
    List.isEmpty_nil, Bool.not_true, hp, Bool.or_false, TyS.data, TyM.dataRec?, TyM.err]
  rw [hf]
  simp only [hsol, if_true]
  rw [if_pos (.inl rfl)]
  show SM.strictS K.dm.read (ctorOut K.dm d c fs (some (K.dm.recOf d (solved sol)))) s' = _
  simp only [SM.strictS, ctorOut, hs, Bool.false_eq_true, if_false, pure]
  rw [if_pos (by exact hm)]
  rfl

end Ochr.Meaning.Regress.AdequacyFlip

namespace Ochr.Meaning.Regress.AdequacyFlip
open Ochr Ochr.Meaning

variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The audit's A1, in the static form (docs/31 D29): [Access] of a place ends the borrows lent at,
over or under it, so reading the second field of a pair leaves a borrow of the first field live
(its site is not comparable with the path read), and reading the pair whole ends it. Before D29
this was stated on what the observed content depends on (`obsDep`), which the static access no
longer consults. (The checker accepts the program this models only through a borrow's content
since main's D90, whose known gap F4 makes a field read of a known pair a one-arm match whose
entry reads the whole pair: `AdequacyProbes2.Disjoint`, now rejected.) -/
theorem access_other_field (s : SState) (p : Pos) (l : Nat)
    (hl : s.lent l = [⟨p, [.proj 0], false⟩]) :
    s.reached p (dataHit [.proj 1]) l = false ∧ s.reached p (dataHit []) l = true := by
  simp [SState.reached, hl, dataHit, pathKey, Step.key]
  decide

/-- The audit's A16: a checker binding whose stored type is a Π-type reads, in the reference state,
as the code its Π-term runs to in the frame of its captures, so it can be called (before D59 it
was read with that Π's shape, `tyShape`; before that with none, and `callOf` failed). -/
theorem stored_pi_code (caps : List Value) (hs : List Hint) (ds : List Term) (c : Term) (rd : List (DeclInfo × Value))
    -- the strict Π-closure: its captures are typed, and so are its domains and codomain
    (hcap : CapsOk K.dm.read (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))
    (hok : PiOk K.dm.read (runDoms K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))) ds) []
      (codOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd)))
          (bindsOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))) ds) (ds.map Term.isRefTy) c)) :
    (Value.tyS K.dm K.M K.Γ ρ (.tPi caps (.pi hs ds c) rd)).m =
      piTyAt K.dm.read (K.D.piSort (scopeOf (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))))
          (.pi hs ds c))
        (runDoms K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))) ds)
        (codOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd)))
          (bindsOf K ρ noFuture (stateOf 0 (capsState (capsVals K ρ noFuture caps) (capsTys K ρ noFuture rd))) ds) (ds.map Term.isRefTy) c) := by
  show (meanV K ρ noFuture (.plain .err) (.tPi caps (.pi hs ds c) rd)).asTy = _
  rw [meanV, if_pos hcap, run_pi_def, if_pos hok]
  rfl

/-- The audit's A10: a closure's capture whose recorded type is a Π-type is bound at that type's
code (before, `capsTys` read every recorded type as `.plain _`; then with its shape). -/
theorem captured_pi_code (d : DeclInfo) (caps : List Value) (t : Term) (rd rest : List (DeclInfo × Value)) :
    (capsTys K ρ φ ((d, .tPi caps t rd) :: rest)).head?
      = some (d, .plain (meanV K ρ φ (.plain .err) (.tPi caps t rd)).asTy) := by
  rw [capsTys]; rfl

/-- R6: a parameter whose domain term is a Π-type is bound at the code that term runs to, so it
can be called (`Regress/NoShape_R6.lean` records the failure before: a parameter was bound at
`.plain _`). The `.fix` clause's frame binds parameter `i` at `(runBinds …)[i].1 acc`. -/
theorem pi_param_code (s : SState) (dcs : List DeclInfo) (pre : List PBind) (rs : List Bool) (hs : List Hint)
    (ds : List Term) (c : Term) (acc : List Sem)
    (hok : PiOk K.dm.read (runDoms K ρ φ (extendBy s pre rs acc) ds) []
      (codOf K ρ φ (extendBy s pre rs acc) (bindsOf K ρ φ (extendBy s pre rs acc) ds) (ds.map Term.isRefTy) c)) :
    ((mkBind dcs pre fun acc => run K ρ φ (.plain .err) (.pi hs ds c) (extendBy s pre rs acc)).1 acc).m
      = piTyAt K.dm.read (K.D.piSort (scopeOf (extendBy s pre rs acc)) (.pi hs ds c)) (runDoms K ρ φ (extendBy s pre rs acc) ds)
          (codOf K ρ φ (extendBy s pre rs acc) (bindsOf K ρ φ (extendBy s pre rs acc) ds) (ds.map Term.isRefTy) c) := by
  simp only [mkBind, run, run_pi_def]
  rw [if_pos hok]
  rfl

/-- ... and that binder is the one `runBinds` gives a Π-typed parameter. -/
theorem runBinds_pi (s : SState) (dcs : List DeclInfo) (pre : List PBind) (rs : List Bool) (hs : List Hint)
    (ds : List Term) (c : Term) (rest : List Term) :
    (runBinds K ρ φ s dcs pre rs (.pi hs ds c :: rest)).head?
      = some (mkBind dcs pre fun acc => run K ρ φ (.plain .err) (.pi hs ds c) (extendBy s pre rs acc)) := by
  simp only [runBinds, List.head?_cons]

end Ochr.Meaning.Regress.AdequacyFlip
