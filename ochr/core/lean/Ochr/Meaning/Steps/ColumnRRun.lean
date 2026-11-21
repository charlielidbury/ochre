import Ochr.Meaning.Steps.RecR
import Ochr.Meaning.Steps.ColumnPRun
import Ochr.Meaning.Steps.ColumnJ

/-!
# The column `R`: the reference's run of the body, and of the checker's sealed value (lead17, 2026-11-21; docs/31 D134)

The reference does not split: `runT`'s `.matchNat` reads the number at `n`, runs the arm it selects, then
drops at the join. From every reference state that reads like one related to `R`'s start state (`ColumnP.RefP`: no
live label, `n` at `(1, 1)` holding `ρ₀ 0` at `Nat`, the function's own binding at `(1, 0)` holding `g`), at a table
deciding as the checker does (`ParDecR`), at any assignment `ρ` (the body reads none: `ρ₀` only names the number at
`n`):

- `ρ₀ 0 = 0`: the result `0` at `Nat`, `n` moved (as `P`);
- `ρ₀ 0 = a + 1`: the arm is the CALL `R(n.0)`: the head reads `g` in place (a copy: the binding keeps it), the
  argument's read gives `a` at `Nat` and writes `moved` at the predecessor (`ColumnP.setN0`), then `callOf` of `g`
  at `a` (`runCallR`); the join writes `moved` at `n`.

And the meaning of the checker's value at the call, the sealed program `⌈R(σ1)⌉`, is the run of its term from the
empty state, `callOf` of the context's `R` at `ρ σ1` (`mean_vR`). Where the context's `R` is the function's own
binding's value (`K_b`, docs/31 D134), the two are the same call.
-/

namespace Ochr.Meaning.Steps.Form.ColumnR

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form
open Ochr.Meaning.Steps.Form.ColumnP (RI pn0 RefJ RefP dropN setN0 accessLentPrefix_nil lentPrefix_nil)

/-- **The decisions the reference's run of `R`'s body reads** (a table aligned with the checker at `stR` makes them,
`parDecR`): the body, the call and the argument's read are neither statements nor proofs, `n` and `n.0` are moved,
the join of the match with nothing moved at entry moves `n`; and the sealed call `⌈R(σ1)⌉`, run from the empty
state, is neither a statement nor a proof. -/
def ParDecR (D : Decisions) : Prop :=
  D.flags RI bodyR = (false, false) ∧ D.flags RI callR = (false, false) ∧ D.flags RI (.place pn0) = (false, false) ∧
    D.copy (D.placeDecl RI pn0) = false ∧ D.copy (D.placeDecl RI (.var 0)) = false ∧
    D.joinMoves RI [] bodyR = [.var 0] ∧ D.flags [] sealR = (false, false)

section
variable {K : RunCtx} {ρ ρ₀ : Assignment} {φ : Future} {g : Sem} {s : SState}

/-- **The join's drop of `R`'s match** (`ColumnP.joinP` with `R`'s match). -/
theorem joinR (hd : ParDecR K.D) (h : RefJ s) :
    JoinDropOk K φ [] bodyR s ∧ joinDrop K φ [] bodyR s = dropN K s := by
  have hjm : K.D.joinMoves (scopeOf s) [] bodyR = [.var 0] := by rw [h.scope]; exact hd.2.2.2.2.2.1
  have hcp : K.D.copy (K.D.placeDecl (scopeOf s) (.var 0)) = false := by rw [h.scope]; exact hd.2.2.2.2.1
  have hdrop : dropAt K φ (.var 0) (.bind 1 1) [] s = dropN K s := by
    unfold dropAt; rw [h.shape]; dsimp only
    rw [h.access, hcp, if_neg (by simp), if_pos (fun _ _ => by rw [Sem.updAt.eq_def]; rfl)]
    rfl
  refine ⟨?_, ?_⟩
  · unfold JoinDropOk; rw [hjm]
    refine ⟨?_, trivial⟩
    unfold JoinStepOk; rw [h.resolve0]; dsimp only
    refine ⟨by unfold LentPrefixOk; rw [lentPrefix_nil]; trivial, ?_⟩
    rw [accessLentPrefix_nil]
    unfold DropOk; rw [h.shape]; dsimp only
    intro _ _; exact h.accessOk K φ _ _
  · unfold joinDrop; rw [hjm]
    simp only [List.foldl_cons, List.foldl_nil, h.resolve0, accessLentPrefix_nil]
    exact hdrop

/-- The argument's read: `n.0` on `n ↦ a + 1` gives `a` at `Nat` and writes `moved` at the predecessor
(`ColumnP.runArmS` at `R`'s table). -/
theorem runArgR (hd : ParDecR K.D) (h : RefP ρ₀ φ g s) {a : Nat} (h0 : ρ₀ 0 = .el0 Nat (a + 1)) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint (.place pn0) s = some ((.el0 Nat a, .plain TyM.nat), setN0 K s) := by
  have hfl : K.D.flags (scopeOf s) (.place pn0) = (false, false) := by rw [h.scope]; exact hd.2.2.1
  have hcp : K.D.copy (K.D.placeDecl (scopeOf s) pn0) = false := by rw [h.scope]; exact hd.2.2.2.1
  have hco : contentOf K φ pn0 s = some ((.el0 Nat a, .plain TyM.nat, .bind 1 1, [.proj 0]), s) := by
    unfold contentOf; rw [h.resolveN0]; dsimp only
    rw [h.access, h.typedFuture, h.valN, h0]
    simp [Sem.follow, Sem.step, Sem.asNat_el0, TyS.plain]
  have hset : setContent K φ (.bind 1 1) [.proj 0] .moved s = some (⟨⟩, setN0 K s) := by
    unfold setContent
    rw [if_pos]
    · rfl
    · intro ψ hψ
      rw [h.typedFut K hψ, h.valN, h0, Sem.updAt.eq_def]
      simp only [Sem.asNat_el0]
      rw [Sem.updAt.eq_def]; rfl
  rw [runT]
  show SM.erasedIf (K.D.flags (scopeOf s) (.place pn0))
    (SM.guarded (ContentOk K φ pn0) (readPlace K φ pn0 (K.D.copy (K.D.placeDecl (scopeOf s) pn0)))) s = _
  rw [hfl, hcp]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  rw [SM.guarded_of (by unfold ContentOk; rw [h.resolveN0]; exact h.accessOk K φ _ _)]
  unfold readPlace
  rw [hco]
  have hwhole : (Sem.el0 Nat a).whole := by simp [Sem.whole]
  have hrg : ReadGood K.dm.read (TyS.plain TyM.nat).m (.el0 Nat a) := .inl ⟨a, rfl⟩
  simp only [bind, Option.bind, hwhole, hrg, not_true_eq_false, if_false, Bool.false_eq_true, List.isEmpty_cons, hset]
  rfl

theorem refP_resolve1 (h : RefP ρ₀ φ g s) : resolve s (.var 1) = some (.bind 1 0, []) := by
  unfold resolve; rw [show (Place.var 1).steps = (1, []) from rfl]; simp [h.varPos1]

/-- **The recursive call `R(n.0)`, in the reference**: the head reads the function's own binding in place (a copy,
at its stored type `T`; the read asks the value whole and a member of `T`), the argument's read gives `a`, the borrow
test is vacuous, then `callOf`. At any tail flag and hint. -/
theorem runCallR (hd : ParDecR K.D) (h : RefP ρ₀ φ g s) {T : TyM} (hts : (s.tyAt (.bind 1 0)).m = T)
    (hgw : g.whole) (hgm : ReadGood K.dm.read T g) {a : Nat} (h0 : ρ₀ 0 = .el0 Nat (a + 1)) (tl : Bool) (hint : TyS) :
    runT K ρ φ tl hint callR s = callOf K.dm.read (g, .plain T) [(.el0 Nat a, .plain TyM.nat)] (setN0 K s) := by
  have hfl : K.D.flags (scopeOf s) callR = (false, false) := by rw [h.scope]; exact hd.2.1
  have hT : ({ s.tyAt (.bind 1 0) with label := none } : TyS) = .plain T := by
    show (⟨(s.tyAt (.bind 1 0)).m, none⟩ : TyS) = ⟨T, none⟩; rw [hts]
  have hco : contentOf K φ (.var 1) s = some ((g, s.tyAt (.bind 1 0), .bind 1 0, []), s) := by
    unfold contentOf; rw [refP_resolve1 h]; dsimp only; rw [h.access, h.typedFuture, h.valSelf]; simp [Sem.follow]
  have hrg : ReadGood K.dm.read (s.tyAt (.bind 1 0)).m g := by rw [hts]; exact hgm
  have h1 : SM.guarded (ContentOk K φ (.var 1)) (readPlace K φ (.var 1) true) s = some ((g, .plain T), s) := by
    rw [SM.guarded_of (by unfold ContentOk; rw [refP_resolve1 h]; exact h.accessOk K φ _ _)]
    unfold readPlace; rw [hco]
    simp only [bind, Option.bind, hgw, hrg, not_true_eq_false, if_false, if_true, hT]
  have h2 : runArgs K ρ φ false T [] [.place pn0] s = some ([(.el0 Nat a, .plain TyM.nat)], setN0 K s) := by
    rw [runArgs]
    simp only [Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false, Bind.bind, Term.argHinted]
    rw [runArgR hd h h0]; rfl
  unfold callR
  rw [runT]
  simp only [show K.D.flags (scopeOf s) (.call (.place (.var 1)) [.place pn0] false) = (false, false) from hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [SM.headOf, Bind.bind, h1]
  rw [show (TyS.plain T).m = T from rfl, h2]
  dsimp only
  rw [if_pos (ColumnJ.borrowArgsTyped_unlabelled _ _ _ _ (fun a ha => by simp at ha; subst ha; rfl))]

/-- **The match, at both tags**: on `0` the arm `Z` and the join's drop; on `a + 1` the call (whose result and state
are given) and the join's drop. In tail position, at any hint. -/
theorem runR (hd : ParDecR K.D) (h : RefP ρ₀ φ g s) (hg : ∀ q, Sem.movedIn g q = []) {T : TyM}
    (hts : (s.tyAt (.bind 1 0)).m = T) (hgw : g.whole) (hgm : ReadGood K.dm.read T g) (hint : TyS) :
    (ρ₀ 0 = .el0 Nat 0 → runT K ρ φ true hint bodyR s = some ((.el0 Nat 0, .plain TyM.nat), dropN K s)) ∧
    (∀ a r, ρ₀ 0 = .el0 Nat (a + 1) →
      callOf K.dm.read (g, .plain T) [(.el0 Nat a, .plain TyM.nat)] (setN0 K s) = some (r, setN0 K s) →
      runT K ρ φ true hint bodyR s = some (r, dropN K (setN0 K s))) := by
  have hfl : K.D.flags (scopeOf s) (.matchNat (.var 0) .zero callR) = (false, false) := by
    rw [h.scope]; exact hd.1
  have htag : TagOk K φ (.var 0) s := by unfold TagOk; rw [h.resolve0]; exact h.accessOk K φ _ _
  have htg : ∀ k, ρ₀ 0 = .el0 Nat k →
      SM.guarded (TagOk K φ (.var 0)) (tagOf K φ (.var 0) natTag) s = some (natTag (.el0 Nat k) (s.tyAt (.bind 1 1)), s) := by
    intro k hk
    rw [SM.guarded_of htag]; unfold tagOf; rw [h.resolve0]; dsimp only
    rw [h.access, h.typedFuture, h.valN, hk]; rfl
  have hme : ∀ t, optCheck (MatchEntryOk K φ (!true) t s) = some ⟨⟩ := fun t => by
    unfold optCheck; rw [if_pos]; intro e; cases e
  have hent : ∀ t, matchEntry K φ (!true) t s = (s, fun _ s₂ => s₂) := fun t => rfl
  have hj : ∀ s', RefJ s' → optCheck (JoinDropOk K φ [] (.matchNat (.var 0) .zero callR) s') = some ⟨⟩ ∧
      joinDrop K φ [] (.matchNat (.var 0) .zero callR) s' = dropN K s' := fun s' h' => by
    obtain ⟨hjok, hjd⟩ := joinR (φ := φ) hd h'
    exact ⟨by unfold optCheck; exact if_pos hjok, hjd⟩
  refine ⟨fun h0 => ?_, fun a r h0 hc => ?_⟩
  · have hz : runT K ρ φ true (.plain TyM.err) .zero s = some ((.el0 Nat 0, .plain TyM.nat), s) := by
      rw [runT]; rfl
    have hmv := h.movedPlaces h0 hg
    have hnt : natTag (.el0 Nat 0) (s.tyAt (.bind 1 1)) = .el0 Nat 0 := by simp [natTag, Sem.asNat_el0]
    show runT K ρ φ true hint (.matchNat (.var 0) .zero callR) s = _
    rw [runT]
    simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
    rw [htg 0 h0, hnt]
    simp only [bind, Option.bind, hent, Sem.asNat_el0, hz, hmv]
    rw [hme, (hj s h.toRefJ).1, (hj s h.toRefJ).2]
  · have hmv := h.movedPlaces h0 hg
    have hnt : natTag (.el0 Nat (a + 1)) (s.tyAt (.bind 1 1)) = .el0 Nat 1 := by simp [natTag, Sem.asNat_el0]
    have harm : runT K ρ φ true (.plain TyM.err) callR s = some (r, setN0 K s) := by
      rw [runCallR hd h hts hgw hgm h0 true (.plain TyM.err), hc]
    have hj₁ : RefJ (setN0 K s) := h.toRefJ.setAt _ _
    show runT K ρ φ true hint (.matchNat (.var 0) .zero callR) s = _
    rw [runT]
    simp only [SM.erasedIf, SM.stmtIf, hfl, Bool.false_eq_true, if_false]
    rw [htg (a + 1) h0, hnt]
    simp only [bind, Option.bind, hent, Sem.asNat_el0, harm, hmv]
    rw [hme, (hj _ hj₁).1, (hj _ hj₁).2]

end

/-! ## The meaning of the checker's value at the call: `⌈R(σ1)⌉` -/

section
variable {K : RunCtx} {ρ : Assignment} {φ : Future}

/-- **The run of the sealed call `R(σ1)` from the empty state**: the head `.val (.gfn "R")` runs to the context's
`R`, the argument `.val σ1` to `ρ 1` at `K.Δ 1`, the borrow test is vacuous, then `callOf`. -/
theorem runT_sealR (hfl : K.D.flags [] sealR = (false, false)) (tl : Bool) (h : TyS) :
    runT K ρ φ tl h sealR (emptyState 0) =
      callOf K.dm.read ((K.C.global "R").1, { (K.C.global "R").2 with label := none })
        [(ρ 1, { K.Δ 1 with label := none })] (emptyState 0) := by
  have h1 : runT K ρ φ false (TyS.plain TyM.err) (Term.val (.gfn "R")) (emptyState 0) =
      some (((K.C.global "R").1, { (K.C.global "R").2 with label := none }), emptyState 0) := by
    rw [runT]; rfl
  have h2 : ∀ T, runArgs K ρ φ false T [] [Term.val (.abs 1)] (emptyState 0) =
      some ([(ρ 1, { K.Δ 1 with label := none })], emptyState 0) := by
    intro T
    rw [runArgs]
    simp only [Bool.false_and, SM.stmtIf, Bool.false_eq_true, if_false, Bind.bind]
    rw [runT]; rfl
  unfold sealR
  rw [runT]
  simp only [show K.D.flags (scopeOf (emptyState 0)) (.call (.val (.gfn "R")) [.val (.abs 1)] true) = (false, false)
    from hfl]
  simp only [SM.erasedIf, SM.stmtIf, Bool.false_eq_true, if_false]
  simp only [SM.headOf, Bind.bind, h1]
  rw [h2]
  dsimp only
  rw [if_pos (ColumnJ.borrowArgsTyped_unlabelled _ _ _ _ (fun a ha => by simp at ha; subst ha; rfl))]

/-- **The meaning of `⌈R(σ1)⌉`**: the result of `callOf` of the context's `R` at `ρ 1`, where that call succeeds. -/
theorem mean_vR (hfl : K.D.flags [] sealR = (false, false)) (hint : TyS) {r : Res} {s' : SState}
    (hc : callOf K.dm.read ((K.C.global "R").1, { (K.C.global "R").2 with label := none })
        [(ρ 1, { K.Δ 1 with label := none })] (emptyState 0) = some (r, s')) :
    meanV K ρ φ hint vR = r.1 := by
  show (match runT K ρ φ false hint sealR (emptyState 0) with | some ((v, _), _) => v | none => .err) = r.1
  rw [runT_sealR hfl, hc]

end

end Ochr.Meaning.Steps.Form.ColumnR
