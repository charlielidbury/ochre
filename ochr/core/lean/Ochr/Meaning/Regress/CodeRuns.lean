import Ochr.Meaning.Regress.CodeClosures
import Ochr.Meaning.Regress.Adequacy_flipped

/-!
# The motivating programs, run in the model (docs/31 D59; built, kernel-checked)

The programs the checker accepts (`Regress/ShapeProbes.lean`, `Regress/AdequacyProbes.lean`) on
which the reference run went wrong while a type's structure was carried beside its meaning, each
now run by the model's own `run`, which gets the checker's answer:

* `UseAdder` (A11): `let a = Adder(2); a(3)` is `5`: the call's result is typed at the code
  `Adder`'s telescope reaches, `Π(m : Nat). Nat`, and `a` is called along it.
* `UseFn` (A18) and `UseFnLet`: `Fn(Nat)` runs to the type value holding `Π(x : Nat). Nat`'s code,
  so the parameter `f : Fn(Nat)` is bound at it, and `f(3)` (or `let g = f; g(3)`) applies `f`.
* `UsePred` (A18 through a predicate type, at `Type₁`): `Pred(Nat)` runs to `Π(x : Nat). Prop`'s
  code at level 1, and `P(3)` applies `P` along it.
* `Alias` (A19): `let T = Π(n : Nat). Nat; let g : T = f; g(3)` applies `f`: `T` holds the code.
* `id` at a function type: `let g = id(Nat → Nat, f); g(Z)` applies `f`: the result is typed at
  the argument's own code (`Type₀`'s elements are codes).
* `BoxProof` (A17): `MkPBox(h)`, `h : True` a proof read at a place, solves `A := True` from `h`'s
  stored type and means `⋆`.

The globals (`Adder`, `Fn`, `Pred`, `id`) are given as the closures the `.fix` clause builds along
their types' codes (`CodeClosures.lean`, with the bodies as functions on meanings); the runs of
their bodies' terms are not run here. The decisions are the trivial ones of `Attack.D₀` (nothing a
statement or a proof, Π-terms at `Type₀`), every place read as a copy; `BoxProof` classes its one
proof read as a proof.
-/

namespace Ochr.Meaning.Regress.CodeRuns
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CodeClosures

/-- The probes' decisions: `Attack.D₀` (nothing a statement or a proof, Π-terms at `Type₀`), with
every place read as a copy (a move would give the same result and leave `⊥` behind). -/
def Dp : Decisions := { Attack.D₀ with «copy» := fun _ => true }

/-- The probes' run context: the given globals, no unknowns, the decisions `Dp`. -/
def Kp (dm : DataModel) (Γ : List IndDecl) (G : String → Sem × TyS) : RunCtx where
  dm := dm
  Γ := Γ
  C := { global := G, sealed := fun _ _ _ _ => .err, clo := fun _ _ _ _ _ => .err,
         pi := fun _ _ _ _ _ => TyM.err, paramTy := fun _ _ _ _ => .plain TyM.err }
  D := Dp

variable (dm : DataModel) (Γ : List IndDecl) (G : String → Sem × TyS) (ρ : Assignment) (φ : Future)

/-- A call, where no term is a statement or a proof: its head, its arguments along the callee's
code, and the application. -/
theorem run_call (f : Term) (args : List Term) (hd : Bool) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.call f args hd) s =
      (SM.headOf f (fun p => readPlace (Kp dm Γ G) φ p true) (run (Kp dm Γ G) ρ φ (.plain TyM.err) f) >>= fun fv =>
        runArgs (Kp dm Γ G) ρ φ false fv.2.m [] args >>= fun as => callOf fv as) s := rfl

theorem run_const (n : String) (hint : TyS) (s : SState) : run (Kp dm Γ G) ρ φ hint (.const n) s = some (G n, s) := rfl

theorem run_letIn (x : Hint) (u w : Term) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.letIn x u w) s =
      (do
        let ((v, T), s) ← run (Kp dm Γ G) ρ φ (.plain .err) u s
        let s := pushBindShaped s { ty := T, val := fun _ => v, decl := .other }
        let ((r, R), s) ← run (Kp dm Γ G) ρ φ hint w s
        let held : Option Nat := match s.env.getLast? with
          | some fr => s.shape (.bind s.topIdx (fr.binds.length - 1))
          | none => none
        let s := match held with | some l => s.endLabel l | none => letLenders s
        some ((r, R), s.dropLast)) := rfl

theorem meanV_num (K : RunCtx) (n : Nat) : ∀ hint : TyS,
    meanV K ρ φ hint (Nat.rec Value.zero (fun _ v => .succ v) n) = .el0 Nat n := by
  induction n with
  | zero => intro _; rfl
  | succ k ih => intro _; show (meanV _ ρ φ _ _).succ = _; rw [ih]; simp [Sem.succ, Sem.asNat, Sem.as]

/-- A number written as a value runs to itself at the hint, the state untouched. -/
theorem run_num (n : Nat) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.val (Nat.rec Value.zero (fun _ v => .succ v) n)) s =
      some ((.el0 Nat n, { hint with label := none }), s) := by
  rw [run_val_def, meanV_num]
  congr 3
  cases n <;> rfl

/-- The numeral `n` as a value. -/
abbrev num (n : Nat) : Term := .val (Nat.rec Value.zero (fun _ v => .succ v) n)

/-- The arguments of a call, numerals: each at its parameter's code, the state untouched. -/
theorem runArgs_num (fT : TyM) (earlier : List Sem) (n : Nat) (s : SState) :
    runArgs (Kp dm Γ G) ρ φ false fT earlier [num n] s =
      some ([(.el0 Nat n, .plain (fT.domAfter earlier))], s) := by
  simp only [runArgs, Bool.false_and]
  show (do let r ← run (Kp dm Γ G) ρ φ (.plain (fT.domAfter earlier)) (num n); _) s = _
  simp only [bind, run_num]
  rfl

/-- A call that fixes no final content leaves every meaning as it was. -/
theorem mapVals_noFix (s : SState) : s.mapVals (fun _ v φ' => v (φ'.updList [])) = s := by
  simp [SState.mapVals, Future.updList]

/-- A call at level 0 to a function with no borrow parameter among the arguments and a data
codomain: the application's result, at the code the telescope reached. -/
theorem callOf_data0 {C : Type} (t : Tel Code0 PUnit C) (F : Sem) (args : List Res) (s : SState) (r : Sem) (T : TyM)
    (hr : (args.zip (telRefsL lvl0 t (args.map (·.1)))).filter (·.2) = [])
    (happ : applyFnL lvl0 t F (args.map (·.1)) = some (.data r T [])) :
    callOf (F, .plain (.t0 C (.pi C t))) args s = some ((r, .plain T), s) := by
  change callOfL lvl0 t F args s = some ((r, TyS.plain T), s)
  unfold callOfL; dsimp only; rw [hr, happ]; simp [mapVals_noFix]

/-! ## `UseAdder`: a function returned by a call is called along its code -/

/-- `Adder` as the `.fix` clause builds it, at its type's code. -/
noncomputable def gAdder : String → Sem × TyS :=
  fun _ => (closureL lvl0 noFuture tAdd (adderBody noFuture), .plain (piTyL lvl0 tAdd))

/-- `Adder(2)` runs to the closure `m ↦ 2 + m`, typed at the code `Π(m : Nat). Nat` that `Adder`'s
telescope reaches. -/
theorem run_adder2 (hint : TyS) (s : SState) :
    run (Kp dm Γ gAdder) ρ φ hint (.call (.const "Adder") [num 2] false) s
      = some ((closureL lvl0 noFuture tNN (addBody 2), .plain (piTyL lvl0 tNN)), s) := by
  obtain ⟨-, -, -, h3, -⟩ := adder_call noFuture
  rw [run_call]
  simp only [SM.headOf, bind, run_const, Option.bind, runArgs_num]
  exact callOf_data0 tAdd _ _ s _ _ (by simp [telRefsL, tAdd, dec_nat]) h3

/-- A closure built along a code is whole. -/
theorem closure_whole (n : Nat) : (closureL lvl0 noFuture tNN (addBody n)).whole := by
  obtain ⟨F, hF⟩ := inner_eq noFuture n
  rw [hF]; simp [Sem.whole]

/-- **`UseAdder` in the model: `let a = Adder(2); a(3)` is `5`.** The checker accepts `UseAdder`
(`AdequacyProbes`); with the result's structure carried beside its meaning, the reference's
binding `a` had no Π-shape and the call `a(3)` failed (the audit's A11). -/
theorem useAdder (hint : TyS) : ∃ T s', run (Kp dm Γ gAdder) ρ φ hint
    (.letIn ⟨"a"⟩ (.call (.const "Adder") [num 2] false) (.call (.place (.var 0)) [num 3] false)) (emptyState 0)
      = some ((.el0 Nat 5, T), s') := by
  obtain ⟨-, -, -, -, h5⟩ := adder_call noFuture
  rw [run_letIn, run_adder2]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, Attack.pushBind_emptyState, run_call]
  simp only [bind, Option.bind]
  erw [AdequacyFlip.head_in_place _ φ _ 0 _ (closure_whole 2)]
  simp only [runArgs_num]
  erw [callOf_data0 tNN _ _ _ _ _ (by simp [telRefsL, tNN, dec_nat]) h5]
  exact ⟨_, _, rfl⟩

/-! ## `UseFn`: a type computed by a call keeps its code -/

/-- `Fn (A : Type) : Type := Π(x : A). A`, at `Type₁`: its parameter ranges over the codes of
`Type₀` types, its codomain is `Type₀`, whose elements are codes. -/
abbrev FnCar : Type 1 := (p : Ty0) → Ty0 × PUnit.{2}

def tFn : Tel lvl1.Code PUnit.{2} FnCar :=
  .param PUnit.{2} false Ty0 .univ1 (fun _ => Ty0 × PUnit.{2}) fun _ => .dat PUnit.{2} Ty0 .univ1

/-- `Fn`'s body, as the `.pi` clause runs `Π(x : A). A` with `A` bound to the argument. -/
noncomputable def fnBody : List Sem → Option BodyOut
  | [a] => some ⟨.ty (piTyAt 1 [⟨false, fun _ => a.asTy⟩] ⟨false, fun _ => a.asTy⟩), [], none⟩
  | _ => none

/-- The code `Π(x : A). A` at a code of `A`, an element of `Type₀`'s decoding. -/
noncomputable def arrowP (p : Ty0) : Ty0 :=
  ⟨(telL lvl0 [⟨false, fun _ => .t0 p.1 p.2.1⟩] [] PUnit ⟨false, fun _ => .t0 p.1 p.2.1⟩).1,
    ⟨.pi _ (telL lvl0 [⟨false, fun _ => .t0 p.1 p.2.1⟩] [] PUnit ⟨false, fun _ => .t0 p.1 p.2.1⟩).2, rfl⟩⟩

/-- `Fn` applied along its code: `Fn(Nat)` is the type value holding `Π(x : Nat). Nat`'s code. -/
theorem fn_apply (φ : Future) :
    applyFnL lvl1 tFn (closureL lvl1 φ tFn fnBody) [.ty TyM.nat]
      = some (.data (.ty (piTyL lvl0 tNN)) (lvl1.toTy Code1.univ1) []) := by
  have hleaf : ∀ p : Ty0, mkTelL lvl1 φ (Tel.dat PUnit.{2} Ty0 .univ1) ([] ++ [lvl1.enc Code1.univ1 p])
      (extMkL false PUnit.{2} Ty0 (fun fs => some (PUnit.unit, fs)) (lvl1.dec Code1.univ1)) fnBody
      = some (arrowP p, PUnit.unit) := by
    intro p
    rw [mkTelL.eq_1]
    show (some ⟨lvl1.enc Code1.univ1 (arrowP p), [], none⟩ : Option BodyOut).bind _ = _
    rw [Option.bind_some]
    unfold mkLeafDataL
    simp only
    rw [show Code1.univ1.dec (Code1.univ1.enc (arrowP p)) = some (arrowP p) from Code1.dec_enc _ _]
    rfl
  have hmk : mkTelL lvl1 φ tFn [] (fun fs => some (PUnit.unit, fs)) fnBody = some fun p => (arrowP p, PUnit.unit) := by
    unfold tFn
    rw [mkTelL.eq_3, dif_pos fun p => by rw [hleaf p]; rfl]
    congr 1
    funext p
    simp only [hleaf p, Option.get_some]
  have hc : closureL lvl1 φ tFn fnBody = .el1 FnCar fun p => (arrowP p, PUnit.unit) := by
    unfold closureL; rw [hmk]
  rw [hc]
  show (Sem.as1 _ (.el1 _ _)).bind (fun F => applyTelL lvl1 tFn (fun _ => []) F [.ty TyM.nat]) = _
  rw [show Sem.as1 FnCar (.el1 _ fun p => (arrowP p, PUnit.unit))
    = some fun p => (arrowP p, PUnit.unit) from lvl1_lawful.unpack_pack _ _, Option.bind_some]
  have hA : Code1.univ1.dec (.ty TyM.nat) = some ⟨Nat, ⟨Code0.nat, rfl⟩⟩ :=
    Code1.dec_enc Code1.univ1 ⟨Nat, ⟨Code0.nat, rfl⟩⟩
  simp only [tFn, applyTelL, lvl1]
  rw [hA]
  rfl

/-- A call at level 1, as `callOf_data0`. -/
theorem callOf_data1 {C : Type 1} (t : Tel Code1 PUnit.{2} C) (F : Sem) (args : List Res) (s : SState) (r : Sem)
    (T : TyM) (hr : (args.zip (telRefsL lvl1 t (args.map (·.1)))).filter (·.2) = [])
    (happ : applyFnL lvl1 t F (args.map (·.1)) = some (.data r T [])) :
    callOf (F, .plain (.t1 C (.pi C t))) args s = some ((r, .plain T), s) := by
  change callOfL lvl1 t F args s = some ((r, TyS.plain T), s)
  unfold callOfL; dsimp only; rw [hr, happ]; simp [mapVals_noFix]

/-- An argument that is the type `Nat` runs to its code, typed at `Type₀`. -/
theorem runArgs_nat (fT : TyM) (earlier : List Sem) (s : SState) :
    runArgs (Kp dm Γ G) ρ φ false fT earlier [.nat] s =
      some ([(.ty TyM.nat, .plain (TyM.univ 1))], s) := by
  simp only [runArgs, Bool.false_and]
  rfl

/-- `Fn` as the `.fix` clause builds it, at its type's code. -/
noncomputable def gFn : String → Sem × TyS :=
  fun _ => (closureL lvl1 noFuture tFn fnBody, .plain (piTyL lvl1 tFn))

/-- `Fn(Nat)` runs to the type value holding `Π(x : Nat). Nat`'s code, from any state. -/
theorem run_fnNat (hint : TyS) (s : SState) :
    run (Kp dm Γ gFn) ρ φ hint (.call (.const "Fn") [.nat] false) s
      = some ((.ty (piTyL lvl0 tNN), .plain (lvl1.toTy Code1.univ1)), s) := by
  rw [run_call]
  simp only [SM.headOf, bind, run_const, Option.bind, runArgs_nat]
  have hA : Code1.univ1.dec (.ty TyM.nat) = some ⟨Nat, ⟨Code0.nat, rfl⟩⟩ :=
    Code1.dec_enc Code1.univ1 ⟨Nat, ⟨Code0.nat, rfl⟩⟩
  exact callOf_data1 tFn _ _ s _ _ (by simp [telRefsL, tFn, hA]) (fn_apply noFuture)

/-- **A parameter typed `Fn(Nat)` is bound at `Π(x : Nat). Nat`'s code** (the `.fix` clause binds a
parameter at the type its domain term runs to, `mkBind`), whatever the frame. -/
theorem fn_param_code (s : SState) (dcs : List DeclInfo) (pre : List PBind) (acc : List Sem) :
    (mkBind dcs pre fun acc => run (Kp dm Γ gFn) ρ φ (.plain .err) (.call (.const "Fn") [.nat] false)
      (extendBy s pre acc)).1 acc = .plain (piTyL lvl0 tNN) := by
  simp only [mkBind, run_fnNat, Sem.asTy]

/-- **`UseFn` in the model**: in a frame binding `f` at `Fn(Nat)`'s code to a function `G`,
`f(3)` is `G(3)`. The checker accepts `UseFn` (`ShapeProbes`); with a type's structure carried
beside its meaning the reference bound `f` with no Π-shape and `f(n)` failed (the audit's A18). -/
theorem useFn (G : NN) (hint : TyS) :
    run (Kp dm Γ gFn) ρ φ hint (.call (.place (.var 0)) [num 3] false)
        (AdequacyFlip.one { ty := .plain (piTyL lvl0 tNN), val := fun _ => .el0 NN G, decl := .other } 0)
      = some ((.el0 Nat (G 3).1, .plain TyM.nat),
          AdequacyFlip.one { ty := .plain (piTyL lvl0 tNN), val := fun _ => .el0 NN G, decl := .other } 0) := by
  rw [run_call]
  simp only [bind, Option.bind]
  rw [AdequacyFlip.head_in_place _ φ _ 0 _ (by simp [Sem.whole])]
  simp only [runArgs_num]
  erw [callOf_data0 tNN _ _ _ _ _ (by simp [telRefsL, tNN, dec_nat]) (apply_any G 3)]

/-! ## Frames of bindings -/

/-- One frame of bindings, no holder. -/
def frame (bs : List SBinding) : SState := { env := [{ binds := bs }], shape := fun _ => none, nextLoan := 0 }

theorem frame_push (bs : List SBinding) (b : SBinding) : (frame bs).pushBind b = frame (bs ++ [b]) := by
  simp [frame, SState.pushBind, SState.topIdx]

theorem frame_liveLabels (bs : List SBinding) : (frame bs).liveLabels = [] := by
  simp [SState.liveLabels, frame, CE4flip.filterMap_none]

/-- A variable of the frame read in place: its meaning at its type, the frame as it was. -/
theorem readPlace_frame (K : RunCtx) (bs : List SBinding) (i : Nat) (b : SBinding) (hi : i < bs.length)
    (hb : bs[bs.length - 1 - i]? = some b) (hw : (b.val φ).whole) :
    readPlace K φ (.var i) true (frame bs) = some ((b.val φ, { b.ty with label := none }), frame bs) := by
  have hr : resolve (frame bs) (.var i) = some (.bind 0 (bs.length - 1 - i), []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, frame, hi]
  have ha := fun hit => CE4flip.access_noshape (frame bs) (.bind 0 (bs.length - 1 - i)) rfl hit
  have hcf : (frame bs).closedFuture φ = φ := by simp [SState.closedFuture, frame_liveLabels]
  simp only [readPlace, contentOf, hr, ha, hcf, bind, Option.bind]
  simp [SState.tyAt, SState.valAt, Sem.follow, frame, hb, hw]

theorem run_place (p : Place) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.place p) s = readPlace (Kp dm Γ G) φ p true s := rfl

/-- A call through a variable of the frame bound at `Π(n : Nat). Nat`'s code, applied to `n`. -/
theorem run_callVar (bs : List SBinding) (i : Nat) (hi : i < bs.length) (Gf : NN) (T : TyS) (hT : T.m = piTyL lvl0 tNN)
    (d : DeclInfo) (hb : bs[bs.length - 1 - i]? = some { ty := T, val := fun _ => .el0 NN Gf, decl := d }) (n : Nat)
    (hint : TyS) :
    run (Kp dm Γ G) ρ φ hint (.call (.place (.var i)) [num n] false) (frame bs)
      = some ((.el0 Nat (Gf n).1, .plain TyM.nat), frame bs) := by
  rw [run_call]
  simp only [bind, Option.bind, SM.headOf]
  rw [readPlace_frame φ _ bs i _ hi hb (by simp [Sem.whole])]
  simp only [runArgs_num]
  obtain ⟨m, l⟩ := T
  simp only at hT; subst hT
  erw [callOf_data0 tNN _ _ _ _ _ (by simp [telRefsL, tNN, dec_nat]) (apply_any Gf n)]

/-! ## `Alias`: a function type bound by a `let` -/

/-- `Π(n : Nat). Nat` runs, in any state, to the type value holding its code, typed at `Type₀`. -/
theorem run_piNN (hs : List Hint) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.pi hs [.nat] .nat) s = some ((.ty (piTyL lvl0 tNN), .plain (TyM.univ 1)), s) := by
  rw [run, run_pi_def]
  rfl

/-- The frame `Alias` starts in: `f : Π(n : Nat). Nat` bound to a function `Gf`. -/
noncomputable def fB (Gf : NN) : SBinding := { ty := .plain (piTyL lvl0 tNN), val := fun _ => .el0 NN Gf, decl := .other }

/-- **`Alias` in the model: `let T = Π(n : Nat). Nat; let g : T = f; g(3)` is `f(3)`.** `T` holds
the type value, whose code the ascription reads, so `g` is bound at it and called along it. The
checker accepts `Alias` (`ShapeProbes`); with the structure carried beside the meaning the
reference's `T` had the shape in its TYPE, the ascription read none, and `g(n)` failed (A19). -/
theorem alias (Gf : NN) (hint : TyS) : ∃ T s', run (Kp dm Γ G) ρ φ hint
    (.letIn ⟨"T"⟩ (.pi [⟨"n"⟩] [.nat] .nat)
      (.letIn ⟨"g"⟩ (.ascribe (.place (.var 1)) (.place (.var 0))) (.call (.place (.var 0)) [num 3] false)))
    (frame [fB Gf]) = some ((.el0 Nat (Gf 3).1, T), s') := by
  have h2 : run (Kp dm Γ G) ρ φ (.plain .err) (.ascribe (.place (.var 1)) (.place (.var 0)))
      (frame [fB Gf, { ty := .plain (TyM.univ 1), val := fun _ => .ty (piTyL lvl0 tNN), decl := .other }])
      = some ((.el0 NN Gf, .plain (piTyL lvl0 tNN)),
          frame [fB Gf, { ty := .plain (TyM.univ 1), val := fun _ => .ty (piTyL lvl0 tNN), decl := .other }]) := by
    rw [run, Attack.run_ascribe (hfl := fun _ _ => rfl)]
    simp only [bind, SM.onCopy]
    rw [show runT (Kp dm Γ G) ρ φ false (.plain .err) (.place (.var 0)) = readPlace (Kp dm Γ G) φ (.var 0) true from rfl,
      readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole])]
    simp only [Option.map, Sem.asTy]
    rw [show runT (Kp dm Γ G) ρ φ false (.plain (piTyL lvl0 tNN)) (.place (.var 1)) = readPlace (Kp dm Γ G) φ (.var 1) true from rfl,
      readPlace_frame φ _ _ 1 _ (by simp) rfl (by simp [Sem.whole, fB])]
    rfl
  rw [run_letIn, run_piNN]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, frame_push, run_letIn]
  simp only [List.singleton_append, List.cons_append, List.nil_append]
  rw [h2]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, frame_push,
    run_callVar dm Γ G ρ φ _ 0 (by simp) Gf _ rfl .other rfl 3]
  exact ⟨_, _, rfl⟩

/-- **`UseFnLet` in the model: `let g = f; g(3)` is `f(3)`**, `f` bound at `Π(n : Nat). Nat`'s code
(as `fn_param_code` binds a parameter typed `Fn(Nat)`): `g` is bound at `f`'s code. -/
theorem useFnLet (Gf : NN) (hint : TyS) : ∃ T s', run (Kp dm Γ G) ρ φ hint
    (.letIn ⟨"g"⟩ (.place (.var 0)) (.call (.place (.var 0)) [num 3] false)) (frame [fB Gf])
      = some ((.el0 Nat (Gf 3).1, T), s') := by
  rw [run_letIn, run_place, readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole, fB])]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, frame_push,
    run_callVar dm Γ G ρ φ _ 0 (by simp) Gf _ rfl .other rfl 3]
  exact ⟨_, _, rfl⟩

/-! ## `let g = id(Nat → Nat, f); g(Z)`: a type argument keeps its code -/

/-- `id` as the `.fix` clause builds it, at its type's code (`Type₁`). -/
noncomputable def gId : String → Sem × TyS := fun _ => (closureL lvl1 noFuture tId idBody, .plain (piTyL lvl1 tId))

/-- **`let g = id(Nat → Nat, f); g(Z)` is `f(Z)` in the model**: the argument `Nat → Nat` runs to
its code, `id`'s first parameter ranges over `Type₀`'s codes, and the result is typed at the
argument's own code, so `g` is bound at it and called along it. The checker accepts it; with
universes decoding to raw Lean types the code would be lost inside `id`, and `g(Z)` would fail. -/
theorem idLet (Gf : NN) (hint : TyS) : ∃ T s', run (Kp dm Γ gId) ρ φ hint
    (.letIn ⟨"g"⟩ (.call (.const "id") [.pi [⟨"n"⟩] [.nat] .nat, .place (.var 0)] false)
      (.call (.place (.var 0)) [num 0] false)) (frame [fB Gf])
      = some ((.el0 Nat (Gf 0).1, T), s') := by
  obtain ⟨-, happ, -⟩ := id_call noFuture Gf
  have hA : Code1.univ1.dec (.ty (piTyL lvl0 tNN)) = some ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩ :=
    Code1.dec_enc Code1.univ1 ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩
  have hx : (Code1.lift NN (Code0.pi NN tNN)).dec (.el0 NN Gf) = some ⟨Gf⟩ :=
    Code1.dec_enc (Code1.lift NN (Code0.pi NN tNN)) ⟨Gf⟩
  have hcall : run (Kp dm Γ gId) ρ φ (.plain .err) (.call (.const "id") [.pi [⟨"n"⟩] [.nat] .nat, .place (.var 0)] false)
      (frame [fB Gf]) = some ((.el0 NN Gf, .plain (piTyL lvl0 tNN)), frame [fB Gf]) := by
    rw [run_call]
    simp only [SM.headOf, bind, run_const, Option.bind, runArgs, Bool.false_and, SM.stmtIf, Bool.false_eq_true,
      if_false]
    rw [show runT (Kp dm Γ gId) ρ φ false (TyS.plain ((gId "id").snd.m.domAfter [])) (Term.pi [⟨"n"⟩] [Term.nat] Term.nat)
        (frame [fB Gf]) = some ((.ty (piTyL lvl0 tNN), .plain (TyM.univ 1)), frame [fB Gf]) from run_piNN dm Γ gId ρ φ _ _ _]
    simp only
    rw [show runT (Kp dm Γ gId) ρ φ false (TyS.plain ((gId "id").snd.m.domAfter ([] ++ [Sem.ty (piTyL lvl0 tNN)])))
        (Term.place (Place.var 0)) = readPlace (Kp dm Γ gId) φ (.var 0) true from rfl,
      readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole, fB])]
    simp only [pure]
    exact callOf_data1 tId _ _ _ _ _ (by simp [telRefsL, tId, hA, hx, fB]) happ
  rw [run_letIn, hcall]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, frame_push,
    run_callVar dm Γ gId ρ φ _ 0 (by simp) Gf _ rfl .other rfl 0]
  exact ⟨_, _, rfl⟩

/-! ## `UsePred`: a predicate type computed by a call, at `Type₁` -/

/-- `Π(x : Nat). Prop` at `Type₁` (`Prop : Type₁`): its carrier and telescope code. -/
abbrev PNCar : Type 1 := (n : ULift.{1} Nat) → ULift.{1} Prop × PUnit.{2}

def tPN : Tel lvl1.Code PUnit.{2} PNCar :=
  .param PUnit.{2} false (ULift.{1} Nat) (.lift Nat .nat) (fun _ => ULift.{1} Prop × PUnit.{2}) fun _ =>
    .dat PUnit.{2} (ULift.{1} Prop) .univ0

/-- It is the code the `.pi` clause builds at `Type₁` from `x : Nat` and the codomain `Prop`. -/
theorem tPN_telL : telL lvl1 [⟨false, fun _ => TyM.nat⟩] [] PUnit ⟨false, fun _ => TyM.univ 0⟩ = ⟨PNCar, tPN⟩ := rfl

/-- The codes of `Type₁` types (`Type₁`'s decoding). -/
abbrev Ty1 : Type 2 := (A : Type 1) × {c : Code1 A // c.level = some 2}

/-- `Pred (A : Type) : Type₁ := Π(x : A). Prop`, at `Type₂`. -/
abbrev PredCar : Type 2 := (p : ULift.{2} Ty0) → Ty1 × PUnit.{3}

def tPred : Tel lvl2.Code PUnit.{3} PredCar :=
  .param PUnit.{3} false (ULift.{2} Ty0) (.lift Ty0 .univ1) (fun _ => Ty1 × PUnit.{3}) fun _ => .dat PUnit.{3} Ty1 .univ2

/-- `Pred`'s body, as the `.pi` clause runs `Π(x : A). Prop` (at `Type₁`) with `A` bound. -/
noncomputable def predBody : List Sem → Option BodyOut
  | [a] => some ⟨.ty (piTyAt 2 [⟨false, fun _ => a.asTy⟩] ⟨false, fun _ => TyM.univ 0⟩), [], none⟩
  | _ => none

/-- The code `Π(x : A). Prop` at a code of `A`, an element of `Type₁`'s decoding. -/
noncomputable def predP (p : ULift.{2} Ty0) : Ty1 :=
  ⟨(telL lvl1 [⟨false, fun _ => .t0 p.down.1 p.down.2.1⟩] [] PUnit ⟨false, fun _ => TyM.univ 0⟩).1,
    ⟨.pi _ (telL lvl1 [⟨false, fun _ => .t0 p.down.1 p.down.2.1⟩] [] PUnit ⟨false, fun _ => TyM.univ 0⟩).2, rfl⟩⟩

/-- `Pred` applied along its code: `Pred(Nat)` is the type value holding `Π(x : Nat). Prop`'s code. -/
theorem pred_apply (φ : Future) :
    applyFnL lvl2 tPred (closureL lvl2 φ tPred predBody) [.ty TyM.nat]
      = some (.data (.ty (piTyL lvl1 tPN)) (lvl2.toTy Code2.univ2) []) := by
  have hleaf : ∀ p : ULift.{2} Ty0, mkTelL lvl2 φ (Tel.dat PUnit.{3} Ty1 .univ2) ([] ++ [lvl2.enc (Code2.lift Ty0 .univ1) p])
      (extMkL false PUnit.{3} (ULift.{2} Ty0) (fun fs => some (PUnit.unit, fs)) (lvl2.dec (Code2.lift Ty0 .univ1)))
      predBody = some (predP p, PUnit.unit) := by
    intro p
    rw [mkTelL.eq_1]
    show (some ⟨lvl2.enc Code2.univ2 (predP p), [], none⟩ : Option BodyOut).bind _ = _
    rw [Option.bind_some]
    unfold mkLeafDataL
    simp only
    rw [show Code2.univ2.dec (Code2.univ2.enc (predP p)) = some (predP p) from Code2.dec_enc _ _]
    rfl
  have hmk : mkTelL lvl2 φ tPred [] (fun fs => some (PUnit.unit, fs)) predBody = some fun p => (predP p, PUnit.unit) := by
    unfold tPred
    rw [mkTelL.eq_3, dif_pos fun p => by rw [hleaf p]; rfl]
    congr 1
    funext p
    simp only [hleaf p, Option.get_some]
  have hc : closureL lvl2 φ tPred predBody = .el2 PredCar fun p => (predP p, PUnit.unit) := by
    unfold closureL; rw [hmk]
  rw [hc]
  show (Sem.as2 _ (.el2 _ _)).bind (fun F => applyTelL lvl2 tPred (fun _ => []) F [.ty TyM.nat]) = _
  rw [show Sem.as2 PredCar (.el2 _ fun p => (predP p, PUnit.unit))
    = some fun p => (predP p, PUnit.unit) from lvl2_lawful.unpack_pack _ _, Option.bind_some]
  have hA : (Code2.lift Ty0 Code1.univ1).dec (.ty TyM.nat) = some ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩ :=
    Code2.dec_enc (Code2.lift Ty0 Code1.univ1) ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩
  simp only [tPred, applyTelL, lvl2]
  rw [hA]
  rfl

/-- A call at level 2, as `callOf_data0`. -/
theorem callOf_data2 {C : Type 2} (t : Tel Code2 PUnit.{3} C) (F : Sem) (args : List Res) (s : SState) (r : Sem)
    (T : TyM) (hr : (args.zip (telRefsL lvl2 t (args.map (·.1)))).filter (·.2) = [])
    (happ : applyFnL lvl2 t F (args.map (·.1)) = some (.data r T [])) :
    callOf (F, .plain (.t2 C (.pi C t))) args s = some ((r, .plain T), s) := by
  change callOfL lvl2 t F args s = some ((r, TyS.plain T), s)
  unfold callOfL; dsimp only; rw [hr, happ]; simp [mapVals_noFix]

/-- `Pred` as the `.fix` clause builds it, at its type's code (`Type₂`). -/
noncomputable def gPred : String → Sem × TyS :=
  fun _ => (closureL lvl2 noFuture tPred predBody, .plain (.t2 PredCar (.pi PredCar tPred)))

/-- `Pred(Nat)` runs to the type value holding `Π(x : Nat). Prop`'s code, from any state. -/
theorem run_predNat (hint : TyS) (s : SState) :
    run (Kp dm Γ gPred) ρ φ hint (.call (.const "Pred") [.nat] false) s
      = some ((.ty (piTyL lvl1 tPN), .plain (lvl2.toTy Code2.univ2)), s) := by
  rw [run_call]
  simp only [SM.headOf, bind, run_const, Option.bind, runArgs_nat]
  have hA : (Code2.lift Ty0 Code1.univ1).dec (.ty TyM.nat) = some ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩ :=
    Code2.dec_enc (Code2.lift Ty0 Code1.univ1) ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩
  exact callOf_data2 tPred _ _ s _ _ (by simp [telRefsL, tPred, hA]) (pred_apply noFuture)

/-- **A parameter typed `Pred(Nat)` is bound at `Π(x : Nat). Prop`'s code**, whatever the frame. -/
theorem pred_param_code (s : SState) (dcs : List DeclInfo) (pre : List PBind) (acc : List Sem) :
    (mkBind dcs pre fun acc => run (Kp dm Γ gPred) ρ φ (.plain .err) (.call (.const "Pred") [.nat] false)
      (extendBy s pre acc)).1 acc = .plain (piTyL lvl1 tPN) := by
  simp only [mkBind, run_predNat, Sem.asTy]

/-- **`UsePred` in the model**: in a frame binding `P` at `Pred(Nat)`'s code to a predicate `Pf`,
`P(3)` is the proposition `Pf(3)`, typed at `Prop`. The checker accepts `UsePred` and rejects
`UsePredBad` (`ShapeProbes`). -/
theorem usePred (Pf : PNCar) (hint : TyS) :
    run (Kp dm Γ G) ρ φ hint (.call (.place (.var 0)) [num 3] false)
        (frame [{ ty := .plain (piTyL lvl1 tPN), val := fun _ => .el1 PNCar Pf, decl := .other }])
      = some ((.ty (TyM.prop (Pf ⟨3⟩).1.down), .plain (TyM.univ 0)),
          frame [{ ty := .plain (piTyL lvl1 tPN), val := fun _ => .el1 PNCar Pf, decl := .other }]) := by
  have hx : (Code1.lift Nat Code0.nat).dec (.el0 Nat 3) = some ⟨3⟩ := Code1.dec_enc (Code1.lift Nat Code0.nat) ⟨3⟩
  have happ : applyFnL lvl1 tPN (.el1 PNCar Pf) [.el0 Nat 3]
      = some (.data (.ty (TyM.prop (Pf ⟨3⟩).1.down)) (TyM.univ 0) []) := by
    show (Sem.as1 PNCar (.el1 PNCar Pf)).bind (fun F => applyTelL lvl1 tPN (fun _ => []) F [.el0 Nat 3]) = _
    rw [show Sem.as1 PNCar (.el1 PNCar Pf) = some Pf from lvl1_lawful.unpack_pack _ _, Option.bind_some]
    simp only [tPN, applyTelL, lvl1, hx]
    rfl
  rw [run_call]
  simp only [bind, Option.bind, SM.headOf]
  rw [readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole])]
  simp only [runArgs_num]
  erw [callOf_data1 tPN _ _ _ _ _ (by simp [telRefsL, tPN, hx]) happ]

/-! ## `BoxProof`: a parameter solved by a proof field's stored type (A17) -/

/-- `inductive PBox (A : Prop) := MkPBox(a : A)`, as the checker records it. -/
def pbox : IndDecl :=
  { name := "PBox", params := [(⟨"A"⟩, .sort 0)], sort := 0, ctors := [("MkPBox", [("a", .place (.var 0))])] }

/-- The decisions of `BoxProof`'s constructor: its one place read, `h`, is a proof (erased). -/
def Db : Decisions := { Dp with flags := fun _ t => match t with | .place _ => (true, true) | _ => (false, false) }

/-- `BoxProof`'s run context: `PBox` declared, any data model. -/
def Kb (dm : DataModel) : RunCtx := { Kp dm [pbox] (fun _ => (.err, .plain TyM.err)) with D := Db }

/-- The frame of `BoxProof`'s body: `h : True`, a proof. -/
def hB : SBinding := { ty := .plain (TyM.prop True), val := fun _ => .proof, decl := .other }

/-- The proof `h`, erased, is `⋆` at its stored type `True` (A17). -/
theorem run_h (hint : TyS) : run (Kb dm) ρ φ hint (.place (.var 0)) (frame [hB])
    = some ((.proof, .plain (TyM.prop True)), frame [hB]) := by
  have hr : resolve (frame [hB]) (.var 0) = some (.bind 0 0, []) := by
    simp [resolve, SState.varPos, SState.topIdx, Ochr.Place.steps, frame]
  have ha := fun hit => CE4flip.access_noshape (frame [hB]) (.bind 0 0) rfl hit
  have hcf : (frame [hB]).closedFuture φ = φ := by simp [SState.closedFuture, frame_liveLabels]
  have hp : placeTy (Kb dm) φ (.var 0) (frame [hB]) = .plain (TyM.prop True) := by
    simp only [placeTy, contentOf, hr, ha, hcf]
    simp [SState.tyAt, SState.valAt, Sem.follow, frame, hB]
    rfl
  rw [run, runT]
  show SM.erasedAt (true, true) _ _ _ = _
  simp only [SM.erasedAt, if_true, hp]

/-- **`BoxProof` in the model: `MkPBox(h)` is `⋆` at `PBox(True)`.** The field `a : A` is the proof
`h`, which the run does not run; since A17 it is typed at `h`'s stored type `True`, which solves
`A := True`, so the constructor's run succeeds. The checker accepts `BoxProof` (`ShapeProbes`);
before A17 the field was typed `err`, `A` stayed unsolved and the run failed. -/
theorem boxProof :
    run (Kb dm) ρ φ (.plain TyM.err) (.ctor "PBox" 0 ⟨"MkPBox"⟩ [] [.place (.var 0)]) (frame [hB])
      = some ((.proof, .plain (dm.tyM pbox [.ty (TyM.prop True)])), frame [hB]) := by
  rw [run, runT]
  show SM.erasedIf (false, false) _ _ = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  have hf : (Kb dm).Γ.find? (·.name == "PBox") = some pbox := rfl
  have hrf : runFields (Kb dm) ρ φ true pbox 0 0 [none] [] [.place (.var 0)] (frame [hB])
      = some (([.proof], [some (.ty (TyM.prop True))]), frame [hB]) := by
    simp only [runFields]
    have hd : (Kb dm).D.declOf (scopeOf (frame [hB])) (Term.place (Place.var 0)) = .other := rfl
    have h0 : ∀ T, runT (Kb dm) ρ φ false T (.place (.var 0)) (frame [hB])
        = some ((.proof, .plain (TyM.prop True)), frame [hB]) := fun T => run_h dm ρ φ T
    simp only [hd, h0, bind, SM.stmtIf, Bool.not_false, Bool.true_and, if_true, Option.map_some]
    rfl
  simp only [hf, runParams, bind, pure]
  rw [show (pbox.sort == 0) = true from rfl]
  erw [hrf]
  rfl

end Ochr.Meaning.Regress.CodeRuns
