import Ochr.Meaning.Regress.CodeClosures
import Ochr.Meaning.Regress.DataCodes
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
open Classical

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
        runArgs (Kp dm Γ G) ρ φ false fv.2.m [] args >>= fun as =>
          fun s => if BorrowArgsTyped dm.read fv as s then callOf dm.read fv as s else none) s := rfl

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

/-- A number written as a value runs to itself at `Nat`, the state untouched. -/
theorem run_num (n : Nat) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.val (Nat.rec Value.zero (fun _ v => .succ v) n)) s =
      some ((.el0 Nat n, .plain TyM.nat), s) := by
  rw [run_val_def, meanV_num]
  congr 3
  cases n <;> rfl

/-- The numeral `n` as a value. -/
abbrev num (n : Nat) : Term := .val (Nat.rec Value.zero (fun _ v => .succ v) n)

/-- The arguments of a call, numerals: each at its parameter's code, the state untouched. -/
theorem runArgs_num (fT : TyM) (earlier : List Sem) (n : Nat) (s : SState) :
    runArgs (Kp dm Γ G) ρ φ false fT earlier [num n] s =
      some ([(.el0 Nat n, .plain TyM.nat)], s) := by
  simp only [runArgs, Bool.false_and]
  show (do let r ← run (Kp dm Γ G) ρ φ (.plain (fT.domAfter dm.read earlier)) (num n); _) s = _
  simp only [bind, run_num]
  rfl

/-- A call that fixes no final content leaves every meaning as it was. -/
theorem mapVals_noFix (s : SState) : s.mapVals (fun _ v φ' => v (φ'.updList [])) = s := by
  simp [SState.mapVals, Future.updList]

/-- A call at level 0 to a function with no borrow parameter among the arguments and a data
codomain: the application's result, at the code the telescope reached. -/
theorem callOf_data0 {C : Type} (t : Tel Code0 PUnit C) (F : Sem) (args : List Res) (s : SState) (r : Sem) (T : TyM)
    (hr : (args.zip (telRefsL (lvl0 dm.read) t (args.map (·.1)))).filter (·.2) = [])
    (happ : applyFnL (lvl0 dm.read) t F (args.map (·.1)) = some (.data r T [])) :
    (if BorrowArgsTyped dm.read (F, .plain (.t0 C (.pi C t))) args s then
      callOf dm.read (F, .plain (.t0 C (.pi C t))) args s else none) = some ((r, .plain T), s) := by
  -- no borrow parameter among the arguments: the strict test has no label to read
  have hb : BorrowArgsTyped dm.read (F, .plain (.t0 C (.pi C t))) args s := by
    intro i l h
    simp only [refLabelsOf, refsOf, TyS.plain, hr, List.map_nil, List.getElem?_nil] at h
    cases h
  rw [if_pos hb]
  change callOfL (lvl0 dm.read) t F args s = some ((r, TyS.plain T), s)
  unfold callOfL; dsimp only; rw [hr, happ]; simp [mapVals_noFix]

/-! ## `UseAdder`: a function returned by a call is called along its code -/

/-- `Adder` as the `.fix` clause builds it, at its type's code. -/
noncomputable def gAdder (R : DataRead) : String → Sem × TyS :=
  fun _ => (closureL (lvl0 R) noFuture tAdd (adderBody R noFuture), .plain (piTyL (lvl0 R) tAdd))

/-- `Adder(2)` runs to the closure `m ↦ 2 + m`, typed at the code `Π(m : Nat). Nat` that `Adder`'s
telescope reaches. -/
theorem run_adder2 (hint : TyS) (s : SState) :
    run (Kp dm Γ (gAdder dm.read)) ρ φ hint (.call (.const "Adder") [num 2] false) s
      = some ((closureL (lvl0 dm.read) noFuture tNN (addBody dm.read 2), .plain (piTyL (lvl0 dm.read) tNN)), s) := by
  obtain ⟨-, -, -, h3, -⟩ := adder_call noFuture
  rw [run_call]
  simp only [SM.headOf, bind, run_const, Option.bind, runArgs_num]
  exact callOf_data0 dm tAdd _ _ s _ _ (by simp [telRefsL, tAdd, dec_nat]) h3

/-- A closure built along a code is whole. -/
theorem closure_whole (n : Nat) : (closureL (lvl0 dm.read) noFuture tNN (addBody dm.read n)).whole := by
  obtain ⟨F, hF⟩ := inner_eq noFuture n
  rw [hF]; simp [Sem.whole]

/-- **`UseAdder` in the model: `let a = Adder(2); a(3)` is `5`.** The checker accepts `UseAdder`
(`AdequacyProbes`); with the result's structure carried beside its meaning, the reference's
binding `a` had no Π-shape and the call `a(3)` failed (the audit's A11). -/
theorem useAdder (hint : TyS) : ∃ T s', run (Kp dm Γ (gAdder dm.read)) ρ φ hint
    (.letIn ⟨"a"⟩ (.call (.const "Adder") [num 2] false) (.call (.place (.var 0)) [num 3] false)) (emptyState 0)
      = some ((.el0 Nat 5, T), s') := by
  obtain ⟨-, -, -, -, h5⟩ := adder_call noFuture
  rw [run_letIn, run_adder2]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, Attack.pushBind_emptyState, run_call]
  simp only [bind, Option.bind]
  erw [AdequacyFlip.head_in_place _ φ _ 0 _ (closure_whole dm 2)]
  simp only [runArgs_num]
  erw [callOf_data0 dm tNN _ _ _ _ _ (by simp [telRefsL, tNN, dec_nat]) h5]
  exact ⟨_, _, rfl⟩

/-! ## `UseFn`: a type computed by a call keeps its code -/

/-- `Fn (A : Type) : Type := Π(x : A). A`, at `Type₁`: its parameter ranges over the codes of
`Type₀` types, its codomain is `Type₀`, whose elements are codes. -/
abbrev FnCar : Type 1 := (p : Ty0) → Ty0 × PUnit.{2}

def tFn : Tel Code1 PUnit.{2} FnCar :=
  .param PUnit.{2} false Ty0 .univ1 (fun _ => Ty0 × PUnit.{2}) fun _ => .dat PUnit.{2} Ty0 .univ1

/-- `Fn`'s body, as the `.pi` clause runs `Π(x : A). A` with `A` bound to the argument. -/
noncomputable def fnBody (R : DataRead) : List Sem → Option BodyOut
  | [a] => some ⟨.ty (piTyAt R 1 [⟨false, fun _ => a.asTy⟩] ⟨false, fun _ => a.asTy⟩), [], none⟩
  | _ => none

/-- The code `Π(x : A). A` at a code of `A`, an element of `Type₀`'s decoding. -/
noncomputable def arrowP (R : DataRead) (p : Ty0) : Ty0 :=
  ⟨(telL (lvl0 R) [⟨false, fun _ => .t0 p.1 p.2.1⟩] [] PUnit ⟨false, fun _ => .t0 p.1 p.2.1⟩).1,
    ⟨.pi _ (telL (lvl0 R) [⟨false, fun _ => .t0 p.1 p.2.1⟩] [] PUnit ⟨false, fun _ => .t0 p.1 p.2.1⟩).2, rfl⟩⟩

/-- `Fn` applied along its code: `Fn(Nat)` is the type value holding `Π(x : Nat). Nat`'s code. -/
theorem fn_apply (φ : Future) :
    applyFnL (lvl1 dm.read) tFn (closureL (lvl1 dm.read) φ tFn (fnBody dm.read)) [.ty TyM.nat]
      = some (.data (.ty (piTyL (lvl0 dm.read) tNN)) ((lvl1 dm.read).toTy Code1.univ1) []) := by
  have hleaf : ∀ p : Ty0, mkTelL (lvl1 dm.read) φ (Tel.dat PUnit.{2} Ty0 .univ1) ([] ++ [(lvl1 dm.read).enc Code1.univ1 p])
      (extMkL false PUnit.{2} Ty0 (fun fs => some (PUnit.unit, fs)) ((lvl1 dm.read).dec Code1.univ1)) (fnBody dm.read)
      = some ((arrowP dm.read) p, PUnit.unit) := by
    intro p
    rw [mkTelL.eq_1]
    show (some ⟨(lvl1 dm.read).enc Code1.univ1 ((arrowP dm.read) p), [], none⟩ : Option BodyOut).bind _ = _
    rw [Option.bind_some]
    unfold mkLeafDataL
    simp only
    rw [show Code1.univ1.dec dm.read (Code1.univ1.enc dm.read ((arrowP dm.read) p)) = some ((arrowP dm.read) p) from Code1.dec_enc dm.read _ _]
    rfl
  have hmk : mkTelL (lvl1 dm.read) φ tFn [] (fun fs => some (PUnit.unit, fs)) (fnBody dm.read) = some fun p => ((arrowP dm.read) p, PUnit.unit) := by
    unfold tFn
    rw [mkTelL.eq_3, dif_pos fun p => by rw [hleaf p]; rfl]
    congr 1
    funext p
    simp only [hleaf p, Option.get_some]
  have hc : closureL (lvl1 dm.read) φ tFn (fnBody dm.read) = .el1 FnCar fun p => ((arrowP dm.read) p, PUnit.unit) := by
    unfold closureL; rw [hmk]
  rw [hc]
  show (Sem.as1 _ (.el1 _ _)).bind (fun F => applyTelL (lvl1 dm.read) tFn (fun _ => []) F [.ty TyM.nat]) = _
  rw [show Sem.as1 FnCar (.el1 _ fun p => ((arrowP dm.read) p, PUnit.unit))
    = some fun p => ((arrowP dm.read) p, PUnit.unit) from (lvl1_lawful dm.read).unpack_pack _ _, Option.bind_some]
  have hA : Code1.univ1.dec dm.read (.ty TyM.nat) = some ⟨Nat, ⟨Code0.nat, rfl⟩⟩ :=
    Code1.dec_enc dm.read Code1.univ1 ⟨Nat, ⟨Code0.nat, rfl⟩⟩
  simp only [tFn, applyTelL, lvl1]
  rw [hA]
  rfl

/-- A call at level 1, as `callOf_data0`. -/
theorem callOf_data1 {C : Type 1} (t : Tel Code1 PUnit.{2} C) (F : Sem) (args : List Res) (s : SState) (r : Sem)
    (T : TyM) (hr : (args.zip (telRefsL (lvl1 dm.read) t (args.map (·.1)))).filter (·.2) = [])
    (happ : applyFnL (lvl1 dm.read) t F (args.map (·.1)) = some (.data r T [])) :
    (if BorrowArgsTyped dm.read (F, .plain (.t1 C (.pi C t))) args s then
      callOf dm.read (F, .plain (.t1 C (.pi C t))) args s else none) = some ((r, .plain T), s) := by
  -- no borrow parameter among the arguments: the strict test has no label to read
  have hb : BorrowArgsTyped dm.read (F, .plain (.t1 C (.pi C t))) args s := by
    intro i l h
    simp only [refLabelsOf, refsOf, TyS.plain, hr, List.map_nil, List.getElem?_nil] at h
    cases h
  rw [if_pos hb]
  change callOfL (lvl1 dm.read) t F args s = some ((r, TyS.plain T), s)
  unfold callOfL; dsimp only; rw [hr, happ]; simp [mapVals_noFix]

/-- An argument that is the type `Nat` runs to its code, typed at `Type₀`. -/
theorem runArgs_nat (fT : TyM) (earlier : List Sem) (s : SState) :
    runArgs (Kp dm Γ G) ρ φ false fT earlier [.nat] s =
      some ([(.ty TyM.nat, .plain (TyM.univ 1))], s) := by
  simp only [runArgs, Bool.false_and]
  rfl

/-- `Fn` as the `.fix` clause builds it, at its type's code. -/
noncomputable def gFn (R : DataRead) : String → Sem × TyS :=
  fun _ => (closureL (lvl1 R) noFuture tFn (fnBody R), .plain (piTyL (lvl1 R) tFn))

/-- `Fn(Nat)` runs to the type value holding `Π(x : Nat). Nat`'s code, from any state. -/
theorem run_fnNat (hint : TyS) (s : SState) :
    run (Kp dm Γ (gFn dm.read)) ρ φ hint (.call (.const "Fn") [.nat] false) s
      = some ((.ty (piTyL (lvl0 dm.read) tNN), .plain ((lvl1 dm.read).toTy Code1.univ1)), s) := by
  rw [run_call]
  simp only [SM.headOf, bind, run_const, Option.bind, runArgs_nat]
  have hA : Code1.univ1.dec dm.read (.ty TyM.nat) = some ⟨Nat, ⟨Code0.nat, rfl⟩⟩ :=
    Code1.dec_enc dm.read Code1.univ1 ⟨Nat, ⟨Code0.nat, rfl⟩⟩
  exact callOf_data1 dm tFn _ _ s _ _ (by simp [telRefsL, tFn, hA]) (fn_apply dm noFuture)

/-- **A parameter typed `Fn(Nat)` is bound at `Π(x : Nat). Nat`'s code** (the `.fix` clause binds a
parameter at the type its domain term runs to, `mkBind`), whatever the frame. -/
theorem fn_param_code (s : SState) (dcs : List DeclInfo) (pre : List PBind) (acc : List Sem) :
    (mkBind dcs pre fun acc => run (Kp dm Γ (gFn dm.read)) ρ φ (.plain .err) (.call (.const "Fn") [.nat] false)
      (extendBy s pre acc)).1 acc = .plain (piTyL (lvl0 dm.read) tNN) := by
  simp only [mkBind, run_fnNat, Sem.asTy]

/-- **`UseFn` in the model**: in a frame binding `f` at `Fn(Nat)`'s code to a function `G`,
`f(3)` is `G(3)`. The checker accepts `UseFn` (`ShapeProbes`); with a type's structure carried
beside its meaning the reference bound `f` with no Π-shape and `f(n)` failed (the audit's A18). -/
theorem useFn (G : NN) (hint : TyS) :
    run (Kp dm Γ (gFn dm.read)) ρ φ hint (.call (.place (.var 0)) [num 3] false)
        (AdequacyFlip.one { ty := .plain (piTyL (lvl0 dm.read) tNN), val := fun _ => .el0 NN G, decl := .other } 0)
      = some ((.el0 Nat (G 3).1, .plain TyM.nat),
          AdequacyFlip.one { ty := .plain (piTyL (lvl0 dm.read) tNN), val := fun _ => .el0 NN G, decl := .other } 0) := by
  rw [run_call]
  simp only [bind, Option.bind]
  rw [AdequacyFlip.head_in_place _ φ _ 0 _ (by simp [Sem.whole])]
  simp only [runArgs_num]
  erw [callOf_data0 dm tNN _ _ _ _ _ (by simp [telRefsL, tNN, dec_nat]) (apply_any G 3)]

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
  have hcf : (frame bs).typedFuture φ = φ := by funext l; simp [SState.typedFuture, frame_liveLabels]
  simp only [readPlace, contentOf, hr, ha, hcf, bind, Option.bind]
  simp [SState.tyAt, SState.valAt, Sem.follow, frame, hb, hw]

theorem run_place (p : Place) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.place p) s = readPlace (Kp dm Γ G) φ p true s := rfl

/-- A call through a variable of the frame bound at `Π(n : Nat). Nat`'s code, applied to `n`. -/
theorem run_callVar (bs : List SBinding) (i : Nat) (hi : i < bs.length) (Gf : NN) (T : TyS) (hT : T.m = piTyL (lvl0 dm.read) tNN)
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
  erw [callOf_data0 dm tNN _ _ _ _ _ (by simp [telRefsL, tNN, dec_nat]) (apply_any Gf n)]

/-! ## `Alias`: a function type bound by a `let` -/

/-- `Π(n : Nat). Nat` runs, in any state, to the type value holding its code, typed at `Type₀`. -/
theorem run_piNN (hs : List Hint) (hint : TyS) (s : SState) :
    run (Kp dm Γ G) ρ φ hint (.pi hs [.nat] .nat) s = some ((.ty (piTyL (lvl0 dm.read) tNN), .plain (TyM.univ 1)), s) := by
  rw [run, run_pi_def]
  rfl

/-- The frame `Alias` starts in: `f : Π(n : Nat). Nat` bound to a function `Gf`. -/
def fB (Gf : NN) : SBinding := { ty := .plain (.t0 NN (.pi NN tNN)), val := fun _ => .el0 NN Gf, decl := .other }

/-- **`Alias` in the model: `let T = Π(n : Nat). Nat; let g : T = f; g(3)` is `f(3)`.** `T` holds
the type value, whose code the ascription reads, so `g` is bound at it and called along it. The
checker accepts `Alias` (`ShapeProbes`); with the structure carried beside the meaning the
reference's `T` had the shape in its TYPE, the ascription read none, and `g(n)` failed (A19). -/
theorem alias (Gf : NN) (hint : TyS) : ∃ T s', run (Kp dm Γ G) ρ φ hint
    (.letIn ⟨"T"⟩ (.pi [⟨"n"⟩] [.nat] .nat)
      (.letIn ⟨"g"⟩ (.ascribe (.place (.var 1)) (.place (.var 0))) (.call (.place (.var 0)) [num 3] false)))
    (frame [fB Gf]) = some ((.el0 Nat (Gf 3).1, T), s') := by
  have h2 : run (Kp dm Γ G) ρ φ (.plain .err) (.ascribe (.place (.var 1)) (.place (.var 0)))
      (frame [fB Gf, { ty := .plain (TyM.univ 1), val := fun _ => .ty (piTyL (lvl0 dm.read) tNN), decl := .other }])
      = some ((.el0 NN Gf, .plain (piTyL (lvl0 dm.read) tNN)),
          frame [fB Gf, { ty := .plain (TyM.univ 1), val := fun _ => .ty (piTyL (lvl0 dm.read) tNN), decl := .other }]) := by
    rw [run, Attack.run_ascribe (hfl := fun _ _ => rfl)]
    simp only [SM.strictS, bind, SM.onCopy]
    rw [show runT (Kp dm Γ G) ρ φ false (.plain .err) (.place (.var 0)) = readPlace (Kp dm Γ G) φ (.var 0) true from rfl,
      readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole])]
    simp only [Option.map, Sem.asTy]
    rw [show runT (Kp dm Γ G) ρ φ false (.plain (piTyL (lvl0 dm.read) tNN)) (.place (.var 1)) = readPlace (Kp dm Γ G) φ (.var 1) true from rfl,
      readPlace_frame φ _ _ 1 _ (by simp) rfl (by simp [Sem.whole, fB])]
    -- the strict ascription: the read carries no label, and `Gf` is a member of its function type
    have hm : Sem.el0 NN Gf ∈ₛ[dm.read] piTyL (lvl0 dm.read) tNN := ⟨Gf, rfl⟩
    simp only [fB, TyS.plain, labTyOk, reduceCtorEq, false_implies, implies_true, if_true]
    rw [if_pos (by exact hm)]
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
noncomputable def gId (R : DataRead) : String → Sem × TyS := fun _ => (closureL (lvl1 R) noFuture tId idBody, .plain (piTyL (lvl1 R) tId))

/-- **`let g = id(Nat → Nat, f); g(Z)` is `f(Z)` in the model**: the argument `Nat → Nat` runs to
its code, `id`'s first parameter ranges over `Type₀`'s codes, and the result is typed at the
argument's own code, so `g` is bound at it and called along it. The checker accepts it; with
universes decoding to raw Lean types the code would be lost inside `id`, and `g(Z)` would fail. -/
theorem idLet (Gf : NN) (hint : TyS) : ∃ T s', run (Kp dm Γ (gId dm.read)) ρ φ hint
    (.letIn ⟨"g"⟩ (.call (.const "id") [.pi [⟨"n"⟩] [.nat] .nat, .place (.var 0)] false)
      (.call (.place (.var 0)) [num 0] false)) (frame [fB Gf])
      = some ((.el0 Nat (Gf 0).1, T), s') := by
  obtain ⟨-, happ, -⟩ := id_call noFuture Gf
  have hA : Code1.univ1.dec dm.read (.ty (piTyL (lvl0 dm.read) tNN)) = some ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩ :=
    Code1.dec_enc dm.read Code1.univ1 ⟨NN, ⟨Code0.pi NN tNN, rfl⟩⟩
  have hx : (Code1.lift NN (Code0.pi NN tNN)).dec dm.read (.el0 NN Gf) = some ⟨Gf⟩ :=
    Code1.dec_enc dm.read (Code1.lift NN (Code0.pi NN tNN)) ⟨Gf⟩
  have hcall : run (Kp dm Γ (gId dm.read)) ρ φ (.plain .err) (.call (.const "id") [.pi [⟨"n"⟩] [.nat] .nat, .place (.var 0)] false)
      (frame [fB Gf]) = some ((.el0 NN Gf, .plain (piTyL (lvl0 dm.read) tNN)), frame [fB Gf]) := by
    rw [run_call]
    simp only [SM.headOf, bind, run_const, Option.bind, runArgs, Bool.false_and, SM.stmtIf, Bool.false_eq_true,
      if_false]
    rw [show runT (Kp dm Γ (gId dm.read)) ρ φ false (TyS.plain (((gId dm.read) "id").snd.m.domAfter (Kp dm Γ (gId dm.read)).dm.read [])) (Term.pi [⟨"n"⟩] [Term.nat] Term.nat)
        (frame [fB Gf]) = some ((.ty (piTyL (lvl0 dm.read) tNN), .plain (TyM.univ 1)), frame [fB Gf]) from run_piNN dm Γ (gId dm.read) ρ φ _ _ _]
    simp only
    rw [show runT (Kp dm Γ (gId dm.read)) ρ φ false (TyS.plain (((gId dm.read) "id").snd.m.domAfter (Kp dm Γ (gId dm.read)).dm.read ([] ++ [Sem.ty (piTyL (lvl0 dm.read) tNN)])))
        (Term.place (Place.var 0)) = readPlace (Kp dm Γ (gId dm.read)) φ (.var 0) true from rfl,
      readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole, fB])]
    simp only [pure]
    exact callOf_data1 dm tId _ _ _ _ _ (by simp [telRefsL, tId, hA, hx, fB]) happ
  rw [run_letIn, hcall]
  simp only [bind, Option.bind]
  rw [Attack.pushBindShaped_noLabel _ _ rfl, frame_push,
    run_callVar dm Γ (gId dm.read) ρ φ _ 0 (by simp) Gf _ rfl .other rfl 0]
  exact ⟨_, _, rfl⟩

/-! ## `UsePred`: a predicate type computed by a call, at `Type₁` -/

/-- `Π(x : Nat). Prop` at `Type₁` (`Prop : Type₁`): its carrier and telescope code. -/
abbrev PNCar : Type 1 := (n : ULift.{1} Nat) → ULift.{1} Prop × PUnit.{2}

def tPN : Tel Code1 PUnit.{2} PNCar :=
  .param PUnit.{2} false (ULift.{1} Nat) (.lift Nat .nat) (fun _ => ULift.{1} Prop × PUnit.{2}) fun _ =>
    .dat PUnit.{2} (ULift.{1} Prop) .univ0

/-- It is the code the `.pi` clause builds at `Type₁` from `x : Nat` and the codomain `Prop`. -/
theorem tPN_telL : telL (lvl1 dm.read) [⟨false, fun _ => TyM.nat⟩] [] PUnit ⟨false, fun _ => TyM.univ 0⟩ = ⟨PNCar, tPN⟩ := rfl

/-- The codes of `Type₁` types (`Type₁`'s decoding). -/
abbrev Ty1 : Type 2 := (A : Type 1) × {c : Code1 A // c.level = some 2}

/-- `Pred (A : Type) : Type₁ := Π(x : A). Prop`, at `Type₂`. -/
abbrev PredCar : Type 2 := (p : ULift.{2} Ty0) → Ty1 × PUnit.{3}

def tPred : Tel Code2 PUnit.{3} PredCar :=
  .param PUnit.{3} false (ULift.{2} Ty0) (.lift Ty0 .univ1) (fun _ => Ty1 × PUnit.{3}) fun _ => .dat PUnit.{3} Ty1 .univ2

/-- `Pred`'s body, as the `.pi` clause runs `Π(x : A). Prop` (at `Type₁`) with `A` bound. -/
noncomputable def predBody (R : DataRead) : List Sem → Option BodyOut
  | [a] => some ⟨.ty (piTyAt R 2 [⟨false, fun _ => a.asTy⟩] ⟨false, fun _ => TyM.univ 0⟩), [], none⟩
  | _ => none

/-- The code `Π(x : A). Prop` at a code of `A`, an element of `Type₁`'s decoding. -/
noncomputable def predP (R : DataRead) (p : ULift.{2} Ty0) : Ty1 :=
  ⟨(telL (lvl1 R) [⟨false, fun _ => .t0 p.down.1 p.down.2.1⟩] [] PUnit ⟨false, fun _ => TyM.univ 0⟩).1,
    ⟨.pi _ (telL (lvl1 R) [⟨false, fun _ => .t0 p.down.1 p.down.2.1⟩] [] PUnit ⟨false, fun _ => TyM.univ 0⟩).2, rfl⟩⟩

/-- `Pred` applied along its code: `Pred(Nat)` is the type value holding `Π(x : Nat). Prop`'s code. -/
theorem pred_apply (φ : Future) :
    applyFnL (lvl2 dm.read) tPred (closureL (lvl2 dm.read) φ tPred (predBody dm.read)) [.ty TyM.nat]
      = some (.data (.ty (piTyL (lvl1 dm.read) tPN)) ((lvl2 dm.read).toTy Code2.univ2) []) := by
  have hleaf : ∀ p : ULift.{2} Ty0, mkTelL (lvl2 dm.read) φ (Tel.dat PUnit.{3} Ty1 .univ2) ([] ++ [(lvl2 dm.read).enc (Code2.lift Ty0 .univ1) p])
      (extMkL false PUnit.{3} (ULift.{2} Ty0) (fun fs => some (PUnit.unit, fs)) ((lvl2 dm.read).dec (Code2.lift Ty0 .univ1)))
      (predBody dm.read) = some ((predP dm.read) p, PUnit.unit) := by
    intro p
    rw [mkTelL.eq_1]
    show (some ⟨(lvl2 dm.read).enc Code2.univ2 ((predP dm.read) p), [], none⟩ : Option BodyOut).bind _ = _
    rw [Option.bind_some]
    unfold mkLeafDataL
    simp only
    rw [show Code2.univ2.dec dm.read (Code2.univ2.enc dm.read ((predP dm.read) p)) = some ((predP dm.read) p) from Code2.dec_enc dm.read _ _]
    rfl
  have hmk : mkTelL (lvl2 dm.read) φ tPred [] (fun fs => some (PUnit.unit, fs)) (predBody dm.read) = some fun p => ((predP dm.read) p, PUnit.unit) := by
    unfold tPred
    rw [mkTelL.eq_3, dif_pos fun p => by rw [hleaf p]; rfl]
    congr 1
    funext p
    simp only [hleaf p, Option.get_some]
  have hc : closureL (lvl2 dm.read) φ tPred (predBody dm.read) = .el2 PredCar fun p => ((predP dm.read) p, PUnit.unit) := by
    unfold closureL; rw [hmk]
  rw [hc]
  show (Sem.as2 _ (.el2 _ _)).bind (fun F => applyTelL (lvl2 dm.read) tPred (fun _ => []) F [.ty TyM.nat]) = _
  rw [show Sem.as2 PredCar (.el2 _ fun p => ((predP dm.read) p, PUnit.unit))
    = some fun p => ((predP dm.read) p, PUnit.unit) from (lvl2_lawful dm.read).unpack_pack _ _, Option.bind_some]
  have hA : (Code2.lift Ty0 Code1.univ1).dec dm.read (.ty TyM.nat) = some ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩ :=
    Code2.dec_enc dm.read (Code2.lift Ty0 Code1.univ1) ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩
  simp only [tPred, applyTelL, lvl2]
  rw [hA]
  rfl

/-- A call at level 2, as `callOf_data0`. -/
theorem callOf_data2 {C : Type 2} (t : Tel Code2 PUnit.{3} C) (F : Sem) (args : List Res) (s : SState) (r : Sem)
    (T : TyM) (hr : (args.zip (telRefsL (lvl2 dm.read) t (args.map (·.1)))).filter (·.2) = [])
    (happ : applyFnL (lvl2 dm.read) t F (args.map (·.1)) = some (.data r T [])) :
    (if BorrowArgsTyped dm.read (F, .plain (.t2 C (.pi C t))) args s then
      callOf dm.read (F, .plain (.t2 C (.pi C t))) args s else none) = some ((r, .plain T), s) := by
  -- no borrow parameter among the arguments: the strict test has no label to read
  have hb : BorrowArgsTyped dm.read (F, .plain (.t2 C (.pi C t))) args s := by
    intro i l h
    simp only [refLabelsOf, refsOf, TyS.plain, hr, List.map_nil, List.getElem?_nil] at h
    cases h
  rw [if_pos hb]
  change callOfL (lvl2 dm.read) t F args s = some ((r, TyS.plain T), s)
  unfold callOfL; dsimp only; rw [hr, happ]; simp [mapVals_noFix]

/-- `Pred` as the `.fix` clause builds it, at its type's code (`Type₂`). -/
noncomputable def gPred (R : DataRead) : String → Sem × TyS :=
  fun _ => (closureL (lvl2 R) noFuture tPred (predBody R), .plain (.t2 PredCar (.pi PredCar tPred)))

/-- `Pred(Nat)` runs to the type value holding `Π(x : Nat). Prop`'s code, from any state. -/
theorem run_predNat (hint : TyS) (s : SState) :
    run (Kp dm Γ (gPred dm.read)) ρ φ hint (.call (.const "Pred") [.nat] false) s
      = some ((.ty (piTyL (lvl1 dm.read) tPN), .plain ((lvl2 dm.read).toTy Code2.univ2)), s) := by
  rw [run_call]
  simp only [SM.headOf, bind, run_const, Option.bind, runArgs_nat]
  have hA : (Code2.lift Ty0 Code1.univ1).dec dm.read (.ty TyM.nat) = some ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩ :=
    Code2.dec_enc dm.read (Code2.lift Ty0 Code1.univ1) ⟨⟨Nat, ⟨Code0.nat, rfl⟩⟩⟩
  exact callOf_data2 dm tPred _ _ s _ _ (by simp [telRefsL, tPred, hA]) (pred_apply dm noFuture)

/-- **A parameter typed `Pred(Nat)` is bound at `Π(x : Nat). Prop`'s code**, whatever the frame. -/
theorem pred_param_code (s : SState) (dcs : List DeclInfo) (pre : List PBind) (acc : List Sem) :
    (mkBind dcs pre fun acc => run (Kp dm Γ (gPred dm.read)) ρ φ (.plain .err) (.call (.const "Pred") [.nat] false)
      (extendBy s pre acc)).1 acc = .plain (piTyL (lvl1 dm.read) tPN) := by
  simp only [mkBind, run_predNat, Sem.asTy]

/-- **`UsePred` in the model**: in a frame binding `P` at `Pred(Nat)`'s code to a predicate `Pf`,
`P(3)` is the proposition `Pf(3)`, typed at `Prop`. The checker accepts `UsePred` and rejects
`UsePredBad` (`ShapeProbes`). -/
theorem usePred (Pf : PNCar) (hint : TyS) :
    run (Kp dm Γ G) ρ φ hint (.call (.place (.var 0)) [num 3] false)
        (frame [{ ty := .plain (piTyL (lvl1 dm.read) tPN), val := fun _ => .el1 PNCar Pf, decl := .other }])
      = some ((.ty (TyM.prop (Pf ⟨3⟩).1.down), .plain (TyM.univ 0)),
          frame [{ ty := .plain (piTyL (lvl1 dm.read) tPN), val := fun _ => .el1 PNCar Pf, decl := .other }]) := by
  have hx : (Code1.lift Nat Code0.nat).dec dm.read (.el0 Nat 3) = some ⟨3⟩ := Code1.dec_enc dm.read (Code1.lift Nat Code0.nat) ⟨3⟩
  have happ : applyFnL (lvl1 dm.read) tPN (.el1 PNCar Pf) [.el0 Nat 3]
      = some (.data (.ty (TyM.prop (Pf ⟨3⟩).1.down)) (TyM.univ 0) []) := by
    show (Sem.as1 PNCar (.el1 PNCar Pf)).bind (fun F => applyTelL (lvl1 dm.read) tPN (fun _ => []) F [.el0 Nat 3]) = _
    rw [show Sem.as1 PNCar (.el1 PNCar Pf) = some Pf from (lvl1_lawful dm.read).unpack_pack _ _, Option.bind_some]
    simp only [tPN, applyTelL, lvl1, hx]
    rfl
  rw [run_call]
  simp only [bind, Option.bind, SM.headOf]
  rw [readPlace_frame φ _ _ 0 _ (by simp) rfl (by simp [Sem.whole])]
  simp only [runArgs_num]
  erw [callOf_data1 dm tPN _ _ _ _ _ (by simp [telRefsL, tPN, hx]) happ]

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

/-- The proof `h`, erased, runs on a copy to `⋆` at `True` (the strict run's C1; before it, A17 typed
an erased place at its stored type, here also `True`). -/
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
  show SM.erasedIf (true, true) _ _ = _
  simp only [SM.erasedIf, if_true]
  rw [show (Kb dm).D.copy ((Kb dm).D.placeDecl (scopeOf (frame [hB])) (.var 0)) = true from rfl,
    readPlace_frame φ _ [hB] 0 hB (by simp) rfl (by simp [Sem.whole, hB])]
  rfl

/-- **`BoxProof` in the model: `MkPBox(h)` is `⋆` at `PBox(True)`.** The field `a : A` is the proof
`h`, which the run does not run; since A17 it is typed at `h`'s stored type `True`, which solves
`A := True`, so the constructor's run succeeds. The checker accepts `BoxProof` (`ShapeProbes`);
before A17 the field was typed `err`, `A` stayed unsolved and the run failed. -/
theorem boxProof
    -- STRICT: `⋆` is a member of `PBox(True)` in the data model
    (hm : Sem.proof ∈ₛ[dm.read] dm.tyM pbox [.ty (TyM.prop True)]) :
    run (Kb dm) ρ φ (.plain TyM.err) (.ctor "PBox" 0 ⟨"MkPBox"⟩ [] [.place (.var 0)]) (frame [hB])
      = some ((.proof, .plain (dm.tyM pbox [.ty (TyM.prop True)])), frame [hB]) := by
  rw [run, runT]
  show SM.erasedIf (false, false) _ _ = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  have hf : (Kb dm).Γ.find? (·.name == "PBox") = some pbox := rfl
  have hrf : runFields (Kb dm) ρ φ true pbox 0 0 none [none] [] [.place (.var 0)] (frame [hB])
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
  show (if ([] : List Term).isEmpty = true ∨ paramsOk dm pbox [] then
    SM.strictS dm.read (ctorOut dm pbox 0 [.proof] (none <|> some (dm.recOf pbox [.ty (TyM.prop True)]))) (frame [hB])
    else none) = _
  rw [if_pos (.inl rfl)]
  simp only [SM.strictS]
  show (if Sem.proof ∈ₛ[dm.read] dm.tyM pbox [.ty (TyM.prop True)] then _ else none) = _
  rw [if_pos hm]
  rfl

/-! ## A recursive and a nested declaration, built and matched by the run (docs/31 D61)

The run's constructor clause builds `Cons(3, Cons(4, Nil))` at `List(Nat)` and
`Node(1, Cons(Node(2, Nil), Nil))` at `Rose(Nat)`, each the value `Regress/DataCodes.lean` shows a
member of its type's code; the match clause reads a value's constructor (`indTag`) and fields
(`Sem.stepField`) off it. The checker's verdicts: `ShapeProbes.LenTwo`, `ShapeProbes.RootOfTree`. -/

open Ochr.Meaning.Regress.DataCodes in
/-- The run's constructor clause at a declaration of `Γ`, nothing a statement or a proof, the
parameters written: the parameters run on copies, the fields at their field types at the
parameters' record, the value is `ctorM` of the fields' meanings (the tree). -/
theorem run_ctor (d : IndDecl) (hd : Γ.find? (·.name == d.name) = some d) (hs : (d.sort == 0) = false)
    (c : Nat) (x : Hint) (ps args : List Term) (hp : ps ≠ []) (hint : TyS) (s : SState)
    (psM : List Sem) (hpm : runParams (Kp dm Γ G) ρ φ d 0 [] ps s = some (psM, s))
    (fs : List Sem) (sol : List (Option Sem))
    (hf : runFields (Kp dm Γ G) ρ φ false d c 0 (some (dm.recOf d psM)) (psM.map some) [] args s = some ((fs, sol), s))
    -- STRICT: the written parameters are members of their types, the value of its type
    (hpo : paramsOk dm d psM) (hm : dm.ctorM d psM c fs ∈ₛ[dm.read] dm.tyM d psM) :
    run (Kp dm Γ G) ρ φ hint (.ctor d.name c x ps args) s
      = some ((dm.ctorM d psM c fs, .plain (dm.tyM d psM)), s) := by
  rw [run, runT]
  show SM.erasedIf (false, false) _ _ = _
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false, bind]
  have hd' : (Kp dm Γ G).Γ.find? (·.name == d.name) = some d := hd
  rw [hd']
  simp only [hpm]
  have hne : (!ps.isEmpty) = true := by cases ps <;> simp_all
  simp only [hne, Bool.true_or, if_true]
  rw [hs]
  erw [hf]
  show (if ps.isEmpty = true ∨ paramsOk dm d psM then
    SM.strictS dm.read (ctorOut dm d c fs (some (dm.recOf d psM))) s else none) = _
  rw [if_pos (.inr hpo)]
  simp only [SM.strictS, ctorOut, hs, Bool.false_eq_true, if_false, pure]
  rw [if_pos (by exact hm)]
  rfl

section Lists
open Ochr.Meaning.Regress.DataCodes Ochr.Meaning.DataModel.Program

/-- `Nil` and `Cons(h, t)` at `List(Nat)`, the parameter written. -/
def nilT : Term := .ctor "List" 0 ⟨"Nil"⟩ [.nat] []
def consT (h : Nat) (t : Term) : Term := .ctor "List" 1 ⟨"Cons"⟩ [.nat] [num h, t]

/-- `Nat` is a member of `Type₀`, the type of `List`'s parameter in the program's data model. -/
theorem paramsOk_psN (d : IndDecl) : paramsOk dmP d psN := by
  intro i v h
  cases i with
  | zero => simp only [psN, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨⟨Nat, Code0.nat, rfl⟩, rfl⟩
  | succ i => simp [psN] at h

theorem runParams_nat (D : IndDecl) (s : SState) :
    runParams (Kp dmP [listD] G) ρ φ D 0 [] [.nat] s = some (psN, s) := rfl

/-- `Nil` runs to the empty list's meaning, at `List(Nat)`. -/
theorem run_nil (hint : TyS) (s : SState) :
    run (Kp dmP [listD] G) ρ φ hint nilT s = some ((semL [], .plain (dmP.tyM listD psN)), s) :=
  run_ctor dmP [listD] G ρ φ listD rfl rfl 0 _ [.nat] [] (by simp) hint s psN (runParams_nat G ρ φ listD s)
    [] _ rfl (paramsOk_psN listD) (semL_memTy [])

/-- `Cons(h, t)` runs to the list's meaning, where `t` runs to the tail's. -/
theorem run_cons (h : Nat) (t : Term) (l : List Nat) (s : SState)
    (ht : ∀ hint, run (Kp dmP [listD] G) ρ φ hint t s = some ((semL l, .plain (dmP.tyM listD psN)), s)) (hint : TyS) :
    run (Kp dmP [listD] G) ρ φ hint (consT h t) s = some ((semL (h :: l), .plain (dmP.tyM listD psN)), s) := by
  have hf : runFields (Kp dmP [listD] G) ρ φ false listD 1 0 (some (dmP.recOf listD psN)) (psN.map some) [] [num h, t] s
      = some (([.el0 Nat h, semL l], psN.map some), s) := by
    have hn : ∀ hint, runT (Kp dmP [listD] G) ρ φ false hint (num h) s = some ((.el0 Nat h, .plain TyM.nat), s) :=
      fun hint => run_num dmP [listD] G ρ φ h hint s
    have ht' : ∀ hint, runT (Kp dmP [listD] G) ρ φ false hint t s = some ((semL l, .plain (dmP.tyM listD psN)), s) := ht
    simp only [runFields, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, bind, Option.bind, hn, ht', pure]
    rfl
  exact run_ctor dmP [listD] G ρ φ listD rfl rfl 1 _ [.nat] [num h, t] (by simp) hint s psN (runParams_nat G ρ φ listD s)
    _ _ hf (paramsOk_psN listD) (semL_memTy (h :: l))

/-- **`Cons(3, Cons(4, Nil))` runs, by the constructor clause, to the list's meaning**, a member of
`List(Nat)`'s code (`DataCodes.semL_memTy`); the match clause reads it as `Cons` (`indTag`) with its
fields (`Sem.stepField`). -/
theorem run_list34 (hint : TyS) (s : SState) :
    run (Kp dmP [listD] G) ρ φ hint (consT 3 (consT 4 nilT)) s = some ((semL [3, 4], .plain (dmP.tyM listD psN)), s) ∧
      indTag (semL [3, 4]) (.plain (dmP.tyM listD psN)) = .el0 Nat 1 ∧
      Sem.stepField dmP [listD] 1 1 (semL [3, 4]) = some (semL [4], .plain (dmP.tyM listD psN)) := by
  refine ⟨run_cons G ρ φ 3 _ [4] s (fun hint => run_cons G ρ φ 4 _ [] s (fun hint => run_nil G ρ φ hint s) hint) hint,
    rfl, rfl⟩

end Lists

section Roses
open Ochr.Meaning.Regress.DataCodes Ochr.Meaning.DataModel.Program

/-- The declarations of the rose-tree program. -/
def ΓR : List IndDecl := [roseD, listD]

/-- `Node(a, ks)` at `Rose(Nat)`; `Nil` and `Cons(r, rs)` at `List(Rose(Nat))`, the parameters written. -/
def nodeT (a : Nat) (ks : Term) : Term := .ctor "Rose" 0 ⟨"Node"⟩ [.nat] [num a, ks]
def rnilT : Term := .ctor "List" 0 ⟨"Nil"⟩ [.tind "Rose" [.nat]] []
def rconsT (r rs : Term) : Term := .ctor "List" 1 ⟨"Cons"⟩ [.tind "Rose" [.nat]] [r, rs]

/-- `Rose(Nat)` is a member of `Type₀`. -/
theorem paramsOk_psR (d : IndDecl) : paramsOk dmP d psR := by
  intro i v h
  cases i with
  | zero => simp only [psR, List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact ⟨⟨_, _, rfl⟩, rfl⟩
  | succ i => simp [psR] at h

theorem runParams_roseNat (s : SState) : runParams (Kp dmP ΓR G) ρ φ roseD 0 [] [.nat] s = some (psN, s) := rfl

/-- `List(Rose(Nat))`'s parameter, the type `Rose(Nat)`, runs to `Rose(Nat)`'s code. -/
theorem runParams_listRose (s : SState) :
    runParams (Kp dmP ΓR G) ρ φ listD 0 [] [.tind "Rose" [.nat]] s = some (psR, s) := rfl

/-- `Nil` at `List(Rose(Nat))` runs to the empty forest. -/
theorem run_lrNil (hint : TyS) (s : SState) :
    run (Kp dmP ΓR G) ρ φ hint rnilT s = some ((nilV, .plain (dmP.tyM listD psR)), s) :=
  run_ctor dmP ΓR G ρ φ listD rfl rfl 0 _ _ [] (by simp) hint s psR (runParams_listRose G ρ φ s) [] _ rfl
    (paramsOk_psR listD) ((DataModel.mem_tyR dmP listD rF rfl _).2 nil_mem)

/-- `Node(a, ks)` runs to the tree, where `ks` runs to the forest. -/
theorem run_node (a : Nat) (ks : Term) (l : Sem) (s : SState)
    (hk : ∀ hint, run (Kp dmP ΓR G) ρ φ hint ks s = some ((l, .plain (dmP.tyM listD psR)), s))
    (hl : dmP.Mem listD rF l) (hint : TyS) :
    run (Kp dmP ΓR G) ρ φ hint (nodeT a ks) s = some ((nodeV a l, .plain (dmP.tyM roseD psN)), s) := by
  have hf : runFields (Kp dmP ΓR G) ρ φ false roseD 0 0 (some (dmP.recOf roseD psN)) (psN.map some) [] [num a, ks] s
      = some (([.el0 Nat a, l], psN.map some), s) := by
    have hn : ∀ hint, runT (Kp dmP ΓR G) ρ φ false hint (num a) s = some ((.el0 Nat a, .plain TyM.nat), s) :=
      fun hint => run_num dmP ΓR G ρ φ a hint s
    have hk' : ∀ hint, runT (Kp dmP ΓR G) ρ φ false hint ks s = some ((l, .plain (dmP.tyM listD psR)), s) := hk
    simp only [runFields, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, bind, Option.bind, hn, hk', pure]
    rfl
  exact run_ctor dmP ΓR G ρ φ roseD rfl rfl 0 _ [.nat] [num a, ks] (by simp) hint s psN (runParams_roseNat G ρ φ s)
    _ _ hf (paramsOk_psN roseD) ((DataModel.mem_tyR dmP roseD rRN rfl _).2 (node_mem a l hl))

/-- `Cons(r, rs)` at `List(Rose(Nat))` runs to the forest. -/
theorem run_lrCons (r rs : Term) (t ts : Sem) (s : SState)
    (hr : ∀ hint, run (Kp dmP ΓR G) ρ φ hint r s = some ((t, .plain (dmP.tyM roseD psN)), s))
    (hrs : ∀ hint, run (Kp dmP ΓR G) ρ φ hint rs s = some ((ts, .plain (dmP.tyM listD psR)), s))
    (ht : dmP.Mem roseD rRN t) (hts : dmP.Mem listD rF ts) (hint : TyS) :
    run (Kp dmP ΓR G) ρ φ hint (rconsT r rs) s = some ((consV t ts, .plain (dmP.tyM listD psR)), s) := by
  have hf : runFields (Kp dmP ΓR G) ρ φ false listD 1 0 (some (dmP.recOf listD psR)) (psR.map some) [] [r, rs] s
      = some (([t, ts], psR.map some), s) := by
    have hr' : ∀ hint, runT (Kp dmP ΓR G) ρ φ false hint r s = some ((t, .plain (dmP.tyM roseD psN)), s) := hr
    have hrs' : ∀ hint, runT (Kp dmP ΓR G) ρ φ false hint rs s = some ((ts, .plain (dmP.tyM listD psR)), s) := hrs
    simp only [runFields, SM.stmtIf, Bool.false_and, Bool.false_eq_true, if_false, bind, Option.bind, hr', hrs', pure]
    rfl
  exact run_ctor dmP ΓR G ρ φ listD rfl rfl 1 _ _ [r, rs] (by simp) hint s psR (runParams_listRose G ρ φ s)
    _ _ hf (paramsOk_psR listD) ((DataModel.mem_tyR dmP listD rF rfl _).2 (cons_mem t ts ht hts))

/-- **`Node(1, Cons(Node(2, Nil), Nil))` (the probe's `Tree`) runs, by the constructor clause, to the
tree**, a member of `Rose(Nat)`'s code (`DataCodes.tree_memTy`); the match clause reads it as `Node`
with its fields, the second a member of `List(Rose(Nat))`'s code. -/
theorem run_tree (hint : TyS) (s : SState) :
    run (Kp dmP ΓR G) ρ φ hint (nodeT 1 (rconsT (nodeT 2 rnilT) rnilT)) s
        = some ((nodeV 1 (consV (nodeV 2 nilV) nilV), .plain (dmP.tyM roseD psN)), s) ∧
      indTag (nodeV 1 (consV (nodeV 2 nilV) nilV)) (.plain (dmP.tyM roseD psN)) = .el0 Nat 0 ∧
      Sem.stepField dmP ΓR 0 1 (nodeV 1 (consV (nodeV 2 nilV) nilV))
        = some (consV (nodeV 2 nilV) nilV, .plain (dmP.tyM listD psR)) := by
  refine ⟨run_node G ρ φ 1 _ _ s (fun hint => run_lrCons G ρ φ _ _ _ _ s
      (fun hint => run_node G ρ φ 2 _ _ s (fun hint => run_lrNil G ρ φ hint s) nil_mem hint)
      (fun hint => run_lrNil G ρ φ hint s) (node_mem 2 _ nil_mem) nil_mem hint)
      (cons_mem _ _ (node_mem 2 _ nil_mem) nil_mem) hint, rfl, rfl⟩

end Roses

end Ochr.Meaning.Regress.CodeRuns
