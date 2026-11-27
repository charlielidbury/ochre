import Ochr.Meaning.Run
import Ochr.Test

/-!
# A data field of a proof, inside an erased match on it (lead36, 2026-11-27; docs/31 D228; the fourth referee's F2)

**The checker** (`Machine.evalMatchByType`, D49): a match on a proof of a declaration that is not a subsingleton (two
constructors, or one with a data field) is a declared proof; its arms must be proofs. Its TYPED check checks each arm
with the data fields bound to FRESH UNKNOWNS (`bindDataFields`: the arm becomes `let w = σ; …`, the field's place renamed
to the new local and every other place shifted; a dependent constructor's proof fields are let-bound too, `⋆` at their
telescope types); its UNTYPED run does not run it (`!typed && !large`: `⋆`). The proof binding itself holds `⋆`
throughout: no constructor value is ever written into it. So inside the arm a borrow of `w` borrows the LOCAL `w`, owned
by itself, a `Nat`: the observation in `G5T(&w)` compares two numbers, and `PExT` computes `G5T(&w)` as `False`.

**The model before docs/31 D228** ran the one arm of such a match with the scrutinee left `•` (`Run.lean`'s `.matchInd`,
`c? = some 0`); a field of `•` reads `•` at the error type (`Sem.stepField`); a borrow is strict (`SM.strictS`), and the
error type has no member. So the model's run FAILS at `&w`, at every state, where the checker's typed run succeeds
(`PB`, `PExT`, `PExF`; a read `clone(w)` succeeds in the model at `err` but binds a value of no type, and a write
`w := 5` fails at the strict test of the value written): the simulation (II) is false at accepted definitions, and so is
the membership of every function whose body holds such a match. The fault is the model's; the checker's reading is the
necessary one (with the coarse one `PEx(Wit(0, refl))` would be a closed proof of `False`).

**Kernel-checked here** (the model's side, at the borrow): `stepField_proof`, `follow_proof_err` (every path below a
field step of `•` reads `•` at the error type), `contentOf_proofField`, `strictBorrow_proofField` (the strict borrow
fails), `runT_borrow_proofField` (the `.borrow` clause fails, whatever its flags) and `runT_letBorrow_proofField` (so does
`let r = &w; t`, `PB`'s arm). That the one arm runs from a state where the scrutinee still means `•` is `Run.lean`'s
`.matchInd` clause as it stood, by reading (`c?`'s `.proof` case).

**The checker's side, pinned by guards** (below): `PB`, `PR`, `PW`, `PExT`, `PExF` accepted, `PEx` rejected; at `PB`'s
body entry `e` holds `⋆`; the typed check runs `PB`'s arm as `let w = σ; let h = (⋆ : …); let r = &w; refl` with `σ`
fresh (`bindDataFields` at the entry state): the borrow's owner is the local `w`, never the proof `e`.
-/

open Ochr.Test

#guard_msgs (drop warning) in
ochr ProofFieldAtk {
  inductive Ex : Prop := Wit(w : Nat, h : Eq(Nat, w, w))
  def G5 (x : &Nat) (e : Id(Unit, *x := 0, *x := 1)) : False := e
  def G5T (x : &Nat) : Prop := Id(Unit, *x := 0, *x := 1)
  def PB (e : Ex) : True := match e { Wit(w, h) => (let r = &w; refl), }
  def PR (e : Ex) : True := match e { Wit(w, h) => (let k = clone(w); refl), }
  def PW (e : Ex) : True := match e { Wit(w, h) => (w := 5; refl), }
  def PExT (e : Ex) : True := match e { Wit(w, h) => (let t : Prop = G5T(&w); let q : Eq(Prop, t, False) = refl; refl), }
  def PExF (e : Ex) : True := match e { Wit(w, h) => (let t : Prop = G5T(&w); let f = (λ(k : t) : Eq(Nat, Z, S(Z)) => match k {}); refl), }
  reject def PEx (e : Ex) : False := match e { Wit(w, h) => G5(&w, refl), }
  def Nest (e : Ex) : True := match e { Wit(w, h) => (w := 5; match e { Wit(w2, h2) => (let q : Eq(Nat, w2, 5) = refl; refl), }), }
  def TwoW (e : Ex) : True := match e { Wit(w, h) => match e { Wit(w2, h2) => (let q : Eq(Nat, w, w2) = refl; refl), }, }
  inductive Succ : Prop := MkSucc(n : Nat, m : Nat, h : Eq(Nat, n, S(m)))
  reject def Boom (e : Succ) : Eq(Nat, Z, S(Z)) := match e { MkSucc(n, m, h) => (n := Z; match e { MkSucc(n2, m2, h2) => match h2 {}, }), }
  inductive Ex2 : Prop := Wit2(a : Nat, b : Nat, h : Eq(Nat, a, b))
  def LocalForm (e : Ex2) : True := match e { Wit2(a, b, h) => (let t : Prop = Id(Unit, a := 0, a := 1); let q : Eq(Prop, t, False) = refl; refl), }
  def EWhole (e : Ex2) : True := match e { Wit2(a, b, h) => (a := 7; let q : Eq(Ex2, e, e) = refl; refl), }
}

namespace Ochr.Meaning.Steps.Form.ProofFieldAtk

open Ochr Ochr.Meaning

-- every verdict as expected: `PB`, `PR`, `PW`, `PExT`, `PExF` accepted, `PEx` rejected
#guard ((Ochr.Test.runWith (some Prelude) "ProofFieldAtk" ProofFieldAtk {} (located := false)).allAsExpected)

/-- The resolved body of a definition of the block. -/
def bodyOf (b : Ochr.Surface.Block) (name : String) : Term :=
  match b.decls.find? (·.name == name) with
  | some d => match Ochr.Surface.runResolve b.decls d 100000 with
    | (.ok (.ok (.defn df)), _) => df.body
    | _ => .zero
  | none => .zero

/-- `PB`'s body as the surface resolves it: a match on `e` (`#0`) with one arm, `let r = &e.w; refl`. -/
def armPB : Term := match bodyOf ProofFieldAtk "PB" with
  | .matchInd _ _ [(_, a)] => a
  | _ => .zero

#guard match bodyOf ProofFieldAtk "PB" with
  | .matchInd (.var 0) "Ex" [(_, .letIn _ (.borrow (.field g (.var 0))) _)] => g.ty == "Ex" && g.ctor == 0 && g.idx == 0
  | _ => false

/-- The checker's state at the entry of `PB`'s body (the function's binding of itself, then `e ↦ ⋆`). -/
def entryPB : Option MState :=
  let r := Ochr.Test.runWith (some Prelude) "ProofFieldAtk" ProofFieldAtk { recordStates := true } (located := true)
  match r.rows.find? (·.name == "PB") with
  | some row => (row.trace.toList.filterMap fun e => match e with
      | .state _ _ _ st => if st.env.size == 2 && st.env[1]!.binds.size == 2 then some st else none
      | _ => none).head?
  | none => none

-- at the entry the proof binding holds `⋆`
#guard entryPB.any fun st => st.env[1]!.binds[1]!.hint.name == "e" && st.env[1]!.binds[1]!.val == .proof

/-- What the typed check runs for `PB`'s arm (`Machine.bindDataFields`, D49 (3)): the data field `w` let-bound to a
fresh unknown, the proof field `h` (a dependent constructor's) let-bound to `⋆` at its telescope type, and the field
place `e.w` renamed to the local `w` (`#1` under `h`). -/
def boundArmPB (st : MState) : Option Term :=
  match st.inds.find? (·.name == "Ex") with
  | some d => match runMachine (Ochr.bindDataFields 1000 (.var 0) d [] 0 armPB) st 100000 with
    | (.ok t _, _, _) => some t
    | _ => none
  | none => none

#guard entryPB.any fun st => match boundArmPB st with
  | some (.letIn w (.val (.abs k)) (.letIn h (.ascribe (.val .proof) _) (.letIn _ (.borrow (.var 1)) _))) =>
      w.name == "w" && h.name == "h" && k == st.absTy.size
  | _ => false
/-! The fifth referee's V2 (docs/18 on `main`, `<sec-referee5>`; docs/31 D231): `Nest`, `TwoW`, `LocalForm`, `EWhole`
accepted and `Boom` rejected (the verdict guard above). In `Nest` the outer rewrite has already renamed the inner match's
pattern variable `w2` (the place `e.w`) to the outer LOCAL `w`, which holds `5` when the inner arm runs: the inner
`Eq(Nat, w2, 5)` is `Eq(Nat, w, 5)`. -/

/-- The checker's state at the entry of a definition's body with one parameter. -/
def entryOf (nm : String) : Option MState :=
  let r := Ochr.Test.runWith (some Prelude) "ProofFieldAtk" ProofFieldAtk { recordStates := true } (located := true)
  match r.rows.find? (·.name == nm) with
  | some row => (row.trace.toList.filterMap fun e => match e with
      | .state _ _ _ st => if st.env.size == 2 && st.env[1]!.binds.size == 2 then some st else none
      | _ => none).head?
  | none => none

/-- The one arm of a body that is a match. -/
def armOf (nm : String) : Term := match bodyOf ProofFieldAtk nm with
  | .matchInd _ _ [(_, a)] => a
  | _ => .zero

#guard (armOf "Nest").pp [] == "#0.w := 5; match #0 { Wit => let q = (refl : Eq(Nat, #0.w, 5)); refl }"
#guard (entryOf "Nest").any fun st => match st.inds.find? (·.name == "Ex") with
  | some d => match runMachine (Ochr.bindDataFields 1000 (.var 0) d [] 0 (armOf "Nest")) st 100000 with
    | (.ok t _, _, _) => t.pp [] == "let w = σ0; let h = ⋆; w := 5; match #2 { Wit => let q = (refl : Eq(Nat, w, 5)); refl }"
    | _ => false
  | none => false

-- the unknown is fresh: the check makes it (Δ grows by one)
#guard entryPB.any fun st => match runMachine (do
    let some d := (← get).inds.find? (·.name == "Ex") | pure 0
    discard (Ochr.bindDataFields 1000 (.var 0) d [] 0 armPB)
    pure (← get).absTy.size) st 100000 with
  | (.ok n _, _, _) => n == st.absTy.size + 1
  | _ => false

end Ochr.Meaning.Steps.Form.ProofFieldAtk

/-! ## The model's side, kernel-checked: a borrow below a field of `•` fails -/

namespace Ochr.Meaning.Steps.Form.ProofFieldAtk

open Ochr Ochr.Meaning

/-- A field of `•` is `•` at the error type. -/
theorem stepField_proof (dm : DataModel) (Γ : List IndDecl) (T : TyS) (c i : Nat) :
    Sem.stepField dm Γ T c i .proof = some (.proof, .plain TyM.err) := rfl

theorem asNat_proof : Sem.asNat .proof = none := rfl

/-- One step on `•` at the error type stays there. -/
theorem step_proof_err (dm : DataModel) (Γ : List IndDecl) (st : Step) :
    Sem.step dm Γ (.plain TyM.err) st .proof = some (.proof, .plain TyM.err) := by
  cases st with
  | deref => rfl
  | proj i =>
    cases i with
    | zero => rfl
    | succ i => rfl
  | field g => rfl

/-- **Every path on `•` at the error type stays there.** -/
theorem follow_proof_err (dm : DataModel) (Γ : List IndDecl) :
    ∀ sts : List Step, Sem.follow dm Γ (.plain TyM.err) .proof sts = some (.proof, .plain TyM.err)
  | [] => rfl
  | st :: sts => by
    simp only [Sem.follow, step_proof_err, Option.bind_some]
    exact follow_proof_err dm Γ sts

/-- **A path that starts with a field step of `•`** reads `•` at the error type. -/
theorem follow_proof_field (dm : DataModel) (Γ : List IndDecl) (T : TyS) (g : FieldRef) (sts : List Step) :
    Sem.follow dm Γ T .proof (.field g :: sts) = some (.proof, .plain TyM.err) := by
  have hs : Sem.step dm Γ T (.field g) .proof = some (.proof, .plain TyM.err) := rfl
  simp only [Sem.follow, hs, Option.bind_some]
  exact follow_proof_err dm Γ sts

end Ochr.Meaning.Steps.Form.ProofFieldAtk

namespace Ochr.Meaning.Steps.Form.ProofFieldAtk

open Ochr Ochr.Meaning

/-- The error type has no member. -/
theorem not_mem_err (R : DataRead) (v : Sem) : ¬ v ∈ₛ[R] TyM.err := by
  rintro ⟨a, _⟩; exact a.elim

section
variable (K : RunCtx) (φ : Future) (p : Place) (s : SState) (pos : Pos) (g : FieldRef) (sts : List Step)

/-- **A place below a field of a binding meaning `•`** (after its access): its content is `•` at the error type. -/
theorem contentOf_proofField (hr : resolve s p = some (pos, .field g :: sts))
    (hv : (s.access pos (dataHit (.field g :: sts))).valAt pos
      ((s.access pos (dataHit (.field g :: sts))).typedFuture φ) = .proof) :
    contentOf K φ p s = some ((.proof, .plain TyM.err, pos, .field g :: sts), s.access pos (dataHit (.field g :: sts))) := by
  simp only [contentOf, hr, hv, follow_proof_field]
  rfl

/-- **The model's strict borrow there fails**: the borrowed content `•` is no member of the error type. -/
theorem strictBorrow_proofField (hr : resolve s p = some (pos, .field g :: sts))
    (hv : (s.access pos (dataHit (.field g :: sts))).valAt pos
      ((s.access pos (dataHit (.field g :: sts))).typedFuture φ) = .proof) :
    SM.strictS K.dm.read (SM.guarded (ContentOk K φ p) (borrowPlace K φ p)) s = none := by
  unfold SM.strictS
  split
  · rename_i r s' h
    obtain ⟨-, h⟩ := SM.guarded_some h
    unfold borrowPlace at h
    rw [contentOf_proofField K φ p s pos g sts hr hv] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Sem.whole, not_true_eq_false, if_false] at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    exact if_neg (not_mem_err _ _)
  · rfl

/-- **The `.borrow` clause fails there**, whatever the table's flags. -/
theorem runT_borrow_proofField (ρ : Assignment) (tl : Bool) (hint : TyS) (hr : resolve s p = some (pos, .field g :: sts))
    (hv : (s.access pos (dataHit (.field g :: sts))).valAt pos
      ((s.access pos (dataHit (.field g :: sts))).typedFuture φ) = .proof) :
    runT K ρ φ tl hint (.borrow p) s = none := by
  have h := strictBorrow_proofField K φ p s pos g sts hr hv
  rw [runT]
  dsimp only
  unfold SM.erasedIf SM.stmtIf
  split <;> simp [h]

/-- **So does `let r = &p; t`** (`PB`'s arm, `p` the field `w` of the proof `e`), whatever the table's flags. -/
theorem runT_letBorrow_proofField (ρ : Assignment) (tl : Bool) (hint : TyS) (x : Hint) (t : Term)
    (hr : resolve s p = some (pos, .field g :: sts))
    (hv : (s.access pos (dataHit (.field g :: sts))).valAt pos
      ((s.access pos (dataHit (.field g :: sts))).typedFuture φ) = .proof) :
    runT K ρ φ tl hint (.letIn x (.borrow p) t) s = none := by
  have h := runT_borrow_proofField K φ p s pos g sts ρ false (.plain TyM.err) hr hv
  rw [runT]
  dsimp only
  unfold SM.erasedIf SM.stmtIf
  split <;> simp [h]

end

end Ochr.Meaning.Steps.Form.ProofFieldAtk

/-! ## After the repair (docs/31 D229): a match on a proof of a non-subsingleton runs no arm -/

namespace Ochr.Meaning.Steps.Form.ProofFieldAtk

open Ochr Ochr.Meaning

/-- **The repaired clause**: where the scrutinee's tag is read (its access passing its strict ends) as `•`, a match on a
proof of a declaration that the table says is not a subsingleton runs no arm, whatever its arms are, and its value is
`•`: so `PB`'s body (and `PExT`'s, `PExF`'s) runs in the model as the checker's untyped run runs it. -/
theorem runT_matchInd_proof_noSub (K : RunCtx) (ρ : Assignment) (φ : Future) (tl : Bool) (hint : TyS) (p : Place)
    (n : String) (arms : List (Hint × Term)) (s s₁ : SState) (hns : K.D.subsingleton n = false)
    (htag : SM.guarded (TagOk K φ p) (tagOf K φ p indTag) s = some (.proof, s₁)) :
    ∃ R s', runT K ρ φ tl hint (.matchInd p n arms) s = some ((.proof, R), s') := by
  rw [runT]
  dsimp only
  unfold SM.erasedIf SM.stmtIf
  simp only [Bind.bind, htag, Option.bind_some, Sem.isProof, Bool.not_true, Bool.false_and, Bool.and_false,
    hns, Bool.false_eq_true, false_and, if_false]
  simp only [optCheck, MatchEntryOk, matchEntry, Bool.false_eq_true, false_implies, if_true, Option.bind_some]
  split <;> (try split) <;> simp_all

end Ochr.Meaning.Steps.Form.ProofFieldAtk
