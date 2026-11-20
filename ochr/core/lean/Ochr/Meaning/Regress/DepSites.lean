import Ochr.Meaning.Regress.CallInPlace
import Ochr.Meaning.DepWithin
import Ochr.Meaning.Regress.StaticLend

/-!
# Dependence within sites, on the concrete states (docs/31 D67, step 2; kernel-checked)

The invariant (`DepWithin.DepWithinSites`): two futures that differ only at live labels with no
site at `p` on a path comparable with `steps` give the same reading of `p` at `steps`, typed or not.
Checked on the lead's states, each the reference's state at that point (by its own run where
the run is computed, else written in the form `callOf`'s `.ref` row (i') and [End] give it, with
the checker's sites where a checker state is at hand):
- the plain borrow, `let y = …; &y` (`Attack.S₂`, `borrowPlace`'s output): holds (`dws_S₂`);
- `Id1`, after `let y = 2; let r = Id1(&y)` and after `*r := 5` (`CallInPlace.SR`): holds;
- `Pick` at `Z`, after `let r = Pick(Z, &a, &b)` (sites: the checker's at `PZAt`): holds;
- `G8` after the re-rooting end of `r`'s borrow, at a known and at an unknown `n` (sites: the
  reference's `relend` on the checker's sites, which `StaticLend` checks equal to the checker's):
  holds;
- the conditional-dependence state (D27's `CondDep`, reachable form, after `k`'s end): holds.
All five hold for the same reason: every position reads only labels lent at it at a path of `*`s
only (a fill at a lent place, a plain loan of a whole binding), which every path at the position is
comparable with (`dws_of_root`).

**The first site below a root** (`SRb`): after `let r = σ1(&c1); let s = &*r` (the attack's
program, by the reference's own run: `Attack.callOf_S₂`, `pushBindShaped_S₃`, then
`borrowPlace_deref_S₄`) `r` reads `s`'s final content and `s` is lent at `(r, [*])`. With paths
compared step by step the invariant failed there (`dwsW_fails_SRb`, kept as the record): `[.0]` at
`r`, a path that skips the `*` (ill-typed: `r` is a borrow), is incomparable with `[*]`, yet reads
the content through it, `*` being the identity on meanings. Since D67's erasure (`pathKey` drops
`*`) the site's key is the root's and the state satisfies it (`dws_SRb`). The further states (a
reborrow of a reborrow, a field borrowed through a returned borrow of a pair) are in
`Regress/DepSitesMore.lean`.
-/

namespace Ochr.Meaning.Regress.DepSites
open Ochr Ochr.Meaning Ochr.Meaning.Regress.CallInPlace

/-- `l` is lent at `p` at a path of `*`s only: the place whole, or a borrow's whole content. -/
def rootSited (s : SState) (p : Pos) (l : Nat) : Bool :=
  (s.lent l).any fun x => decide (x.pos = p) && (pathKey x.path).isEmpty

theorem reached_of_rootSited {s : SState} {p : Pos} {l : Nat} (h : rootSited s p l = true)
    (steps : List Step) : s.reached p (dataHit steps) l = true := by
  unfold rootSited at h
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hp
  refine List.any_eq_true.2 ⟨x, hx, ?_⟩
  simp [hp.1, hp.2, dataHit]

/-- A position each of whose readings reads only labels lent at its root: such a label is reached at
every path, so the futures compared agree on it. -/
theorem dws_of_root (dm : DataModel) (Γ : List IndDecl) (s : SState)
    (hv : ∀ p ψ ψ', (∀ l, ψ l ≠ ψ' l → rootSited s p l = false) → s.valAt p ψ = s.valAt p ψ') :
    DepWithinSites dm Γ s := by
  intro p steps ψ ψ' h
  rw [hv p ψ ψ' fun l hne => by
    have := (h l hne).2
    cases hr : rootSited s p l
    · rfl
    · rw [reached_of_rootSited hr] at this; cases this]

theorem agree_of_rootSited {s : SState} {p : Pos} {ψ ψ' : Future}
    (h : ∀ l, ψ l ≠ ψ' l → rootSited s p l = false) {l : Nat} (hr : rootSited s p l = true) :
    ψ l = ψ' l := by
  refine Classical.byContradiction fun hne => ?_
  rw [h l hne] at hr
  cases hr

variable (dm : DataModel) (Γ : List IndDecl)

/-! ## The plain borrow -/

/-- **The plain borrow** (`borrowPlace_var0_one`'s output): the lender reads the borrow's final
content, lent at its root; the parked borrow reads its old content. -/
theorem dws_S₂ (b : SBinding) (k : Nat) (c : Sem) : DepWithinSites dm Γ (Attack.S₂ b k c) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f <;> rcases i with _ | i
    · have hk := agree_of_rootSited h (l := k) (by simp [rootSited, Attack.S₂])
      simp [SState.valAt, Attack.S₂, hk]
    all_goals simp [SState.valAt, Attack.S₂]
  · rcases f with _ | f <;> rcases i with _ | i <;> simp [SState.valAt, Attack.S₂]

/-! ## `Id1` -/

/-- The frame after `let y = 2; let r = Id1(&y)` (and after a write through `r`): `y` reads a
function of the reborrow `1`'s final content (lent at `y`'s root, a fill), the rest are constant. -/
theorem dws_SR (rT : TyS) (yv rv t0 t1 : SVal) (hy : ∀ ψ ψ' : Future, ψ 1 = ψ' 1 → yv ψ = yv ψ')
    (hr : ∀ ψ ψ', rv ψ = rv ψ') (h0 : ∀ ψ ψ', t0 ψ = t0 ψ') (h1 : ∀ ψ ψ', t1 ψ = t1 ψ') :
    DepWithinSites dm Γ (SR rT yv rv t0 t1) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f <;> rcases i with _ | _ | i
    · have h1' := agree_of_rootSited h (l := 1) (by simp [rootSited, SR])
      simpa [SState.valAt, SR] using hy ψ ψ' h1'
    · simpa [SState.valAt, SR] using hr ψ ψ'
    all_goals simp [SState.valAt, SR]
  · rcases f with _ | f <;> rcases i with _ | _ | i
    · simpa [SState.valAt, SR] using h0 ψ ψ'
    · simpa [SState.valAt, SR] using h1 ψ ψ'
    all_goals simp [SState.valAt, SR]

/-- `y`'s meaning after the call reads only the reborrow's final content. -/
theorem yR1_reads_one (ψ ψ' : Future) (h : ψ 1 = ψ' 1) : yR1 dm ψ = yR1 dm ψ' := by
  unfold yR1
  rw [h]
  split <;> simp [Future.upd]

theorem mv1_const (ψ ψ' : Future) : mv1 dm ψ = mv1 dm ψ' := by
  unfold mv1
  split <;> split <;> rfl

/-- **`Id1`**: after the call and the binding of `r`, and after `*r := 5`. -/
theorem dws_Id1 (TU : TyS) (w : Sem) :
    DepWithinSites dm Γ (SR TU (yR1 dm) (fun _ => w) (mv1 dm) (fun _ => .moved)) :=
  dws_SR dm Γ TU _ _ _ _ (yR1_reads_one dm) (fun _ _ => rfl) (mv1_const dm) (fun _ _ => rfl)

/-! ## `Pick` at `Z`

The reference's state after `let r = Pick(Z, &a, &b)`, in the function's frame (`StaticLend.PZAt`:
frame `1` holds the function's own binding, `a`, `b`, `r`), up to the renaming of labels, taken the
identity as `StaticLend.refOf` takes it. `callOf`'s `.ref` row (i') leaves each lent place reading
its old meaning (its argument label only) at the future fixing the argument labels to the
backward function's components at the decoded final content of the result `0`, or to `err`: a
function of that content alone (`fa`, `fb`, arbitrary here). `r` and the consumed temporaries are
constant. The sites are the checker's (`pz_call`: `0` fills `a` and `b`). -/

def SPZ (S A B R : SBinding) (fa fb : Sem → Sem) (vs vr : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun ψ => fa (ψ 0) },
      { B with val := fun ψ => fb (ψ 0) }, { R with val := fun _ => vr }] [fun _ => .moved, fun _ => .moved, fun _ => .moved]],
    shape := fun p => if p = .bind 1 3 then some 0 else none, nextLoan := 3,
    lent := Env.sitesOf StaticLend.stZ.env,
    heldTy := fun m => if m = 0 then TyM.nat else TyM.err }

theorem rs_PZ_a : (Env.sitesOf StaticLend.stZ.env 0).any (fun x => decide (x.pos = .bind 1 1) && (pathKey x.path).isEmpty) = true := by
  decide +kernel
theorem rs_PZ_b : (Env.sitesOf StaticLend.stZ.env 0).any (fun x => decide (x.pos = .bind 1 2) && (pathKey x.path).isEmpty) = true := by
  decide +kernel

/-- **`Pick` at `Z`.** -/
theorem dws_PZ (S A B R : SBinding) (fa fb : Sem → Sem) (vs vr : Sem) :
    DepWithinSites dm Γ (SPZ S A B R fa fb vs vr) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SPZ]
    · rcases i with _ | _ | _ | _ | i
      · simp [SState.valAt, SPZ]
      · simp [SState.valAt, SPZ, agree_of_rootSited h (l := 0) rs_PZ_a]
      · simp [SState.valAt, SPZ, agree_of_rootSited h (l := 0) rs_PZ_b]
      all_goals simp [SState.valAt, SPZ]
    · simp [SState.valAt, SPZ]
  · rcases f with _ | _ | f
    · simp [SState.valAt, SPZ]
    · rcases i with _ | _ | _ | i <;> simp [SState.valAt, SPZ]
    · simp [SState.valAt, SPZ]

/-! ## `G8` after the re-rooting end, at a known `n` (`G8K`)

After `let r = Pick(S(Z), &a, &b); let s = &*r` and the end of `r`'s borrow `1` (frame `1`: the
function, `a`, `b`, `r`, `s`). Before the end `a`, `b` read functions of `1`'s final content and `r`
reads `s`'s (`3`); [End 1] fixes `1` to what `r` holds, so `a`, `b` read functions of `3`'s final
content, `r` is forgotten (`moved`), `s` holds `3`. The sites: the reference's `relend` on the
checker's sites (`g8k_end`: the checker's after its `endBorrow`): `3` fills `a` and `b`. -/

def SG8K (S A B R T : SBinding) (fa fb : Sem → Sem) (vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { A with val := fun ψ => fa (ψ 3) },
      { B with val := fun ψ => fb (ψ 3) }, { R with val := fun _ => .moved }, { T with val := fun _ => vt }]
      [fun _ => .moved, fun _ => .moved, fun _ => .moved, fun _ => .moved]],
    shape := fun p => if p = .bind 1 4 then some 3 else none, nextLoan := 4,
    lent := (StaticLend.refOf StaticLend.stK.env).relend 1 StaticLend.rK,
    heldTy := fun m => if m = 3 then TyM.nat else TyM.err }

theorem rs_G8K_a : ((StaticLend.refOf StaticLend.stK.env).relend 1 StaticLend.rK 3).any
    (fun x => decide (x.pos = .bind 1 1) && (pathKey x.path).isEmpty) = true := by decide +kernel
theorem rs_G8K_b : ((StaticLend.refOf StaticLend.stK.env).relend 1 StaticLend.rK 3).any
    (fun x => decide (x.pos = .bind 1 2) && (pathKey x.path).isEmpty) = true := by decide +kernel

/-- **`G8` after the re-rooting end, `n` known.** -/
theorem dws_G8K (S A B R T : SBinding) (fa fb : Sem → Sem) (vs vt : Sem) :
    DepWithinSites dm Γ (SG8K S A B R T fa fb vs vt) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SG8K]
    · rcases i with _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SG8K]
      · simp [SState.valAt, SG8K, agree_of_rootSited h (l := 3) rs_G8K_a]
      · simp [SState.valAt, SG8K, agree_of_rootSited h (l := 3) rs_G8K_b]
      all_goals simp [SState.valAt, SG8K]
    · simp [SState.valAt, SG8K]
  · rcases f with _ | _ | f
    · simp [SState.valAt, SG8K]
    · rcases i with _ | _ | _ | _ | i <;> simp [SState.valAt, SG8K]
    · simp [SState.valAt, SG8K]

/-! ## `G8` after the re-rooting end, at an unknown `n`

The same at `G8At` (frame `1`: the function, `n`, `a`, `b`, `r`, `s`), after [End 3]: `n` moved into
the call, `a` and `b` read functions of `s`'s label `4` (the backward function at `ρ`'s `n`, a
constant of the future), `r` forgotten. The sites are written out and tied to the reference's
`relend` on the checker's sites by evaluation: the checker's `G8At` state holds sealed fills whose
re-normalisation calls `Pick`, which the kernel does not run (`StaticLend`). -/

#guard StaticLend.sameSites ((StaticLend.refOf StaticLend.st8.env).relend 3 StaticLend.r8 4)
  (StaticLend.lentK [StaticLend.a8, StaticLend.b8])

def SG8 (S N A B R T : SBinding) (fa fb : Sem → Sem) (vs vt : Sem) : SState :=
  { env := [SFrame.mk [] [], SFrame.mk [{ S with val := fun _ => vs }, { N with val := fun _ => .moved },
      { A with val := fun ψ => fa (ψ 4) }, { B with val := fun ψ => fb (ψ 4) }, { R with val := fun _ => .moved },
      { T with val := fun _ => vt }] [fun _ => .moved, fun _ => .moved, fun _ => .moved, fun _ => .moved]],
    shape := fun p => if p = .bind 1 5 then some 4 else none, nextLoan := 5,
    lent := fun m => if m = 4 then StaticLend.lentK [StaticLend.a8, StaticLend.b8] else [],
    heldTy := fun m => if m = 4 then TyM.nat else TyM.err }

/-- **`G8` after the re-rooting end, `n` unknown.** -/
theorem dws_G8 (S N A B R T : SBinding) (fa fb : Sem → Sem) (vs vt : Sem) :
    DepWithinSites dm Γ (SG8 S N A B R T fa fb vs vt) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | _ | f
    · simp [SState.valAt, SG8]
    · rcases i with _ | _ | _ | _ | _ | _ | i
      · simp [SState.valAt, SG8]
      · simp [SState.valAt, SG8]
      · simp [SState.valAt, SG8, agree_of_rootSited h (l := 4)
          (by simp [rootSited, SG8, StaticLend.lentK, StaticLend.a8])]
      · simp [SState.valAt, SG8, agree_of_rootSited h (l := 4)
          (by simp [rootSited, SG8, StaticLend.lentK, StaticLend.b8])]
      all_goals simp [SState.valAt, SG8]
    · simp [SState.valAt, SG8]
  · rcases f with _ | _ | f
    · simp [SState.valAt, SG8]
    · rcases i with _ | _ | _ | _ | i <;> simp [SState.valAt, SG8]
    · simp [SState.valAt, SG8]

/-! ## The conditional dependence (D27's `CondDep`, reachable form)

A stuck call `σ_f(&x, &y)` returns `k = 0`, filling `x` and `y`; `r` holds it; `j = 1`, `m = 2`
reborrow the fields of its content (`rj = &(*r).0`, `rm = &(*r).1`), lent at `(r, [*, .0])` and
`(r, [*, .1])`. When `k` ends, `relend` passes `k`'s fills to `j` and `m`, and `x` reads
`(back (ψ j, ψ m)).1`, which depends on `m` exactly when `j` holds `0` (`fx`; any injective backward
function is a member's, D27's `back_injective`); `y` reads some function of both (`g`). -/

/-- `x`'s meaning after `k`'s end (D27's `fx`). -/
noncomputable def fx (j m c : Nat) : SVal := fun ψ =>
  open Classical in if ψ j = .el0 Nat 0 then ψ m else .el0 Nat c

/-- The lending before `k`'s end. -/
def lentCD : Nat → List Site := fun l =>
  if l = 0 then [⟨.bind 0 0, [], true⟩, ⟨.bind 0 1, [], true⟩]
  else if l = 1 then [⟨.bind 0 2, [.deref, .proj 0], false⟩]
  else if l = 2 then [⟨.bind 0 2, [.deref, .proj 1], false⟩] else []

/-- The lending after it: the reference's `relend` of `k` at its holder `r`. -/
def lentCD' : Nat → List Site :=
  ({ env := [], shape := fun _ => none, nextLoan := 3, lent := lentCD } : SState).relend 0 (.bind 0 2)

noncomputable def SCD (X Y R J M : SBinding) (c : Nat) (g : Sem → Sem → Sem) (vj vm : Sem) : SState :=
  { env := [SFrame.mk [{ X with val := fx 1 2 c }, { Y with val := fun ψ => g (ψ 1) (ψ 2) },
      { R with val := fun _ => .moved }, { J with val := fun _ => vj }, { M with val := fun _ => vm }] []],
    shape := fun p => if p = .bind 0 3 then some 1 else if p = .bind 0 4 then some 2 else none,
    nextLoan := 3, lent := lentCD' }

theorem rs_CD (l : Nat) (hl : l = 1 ∨ l = 2) (i : Nat) (hi : i = 0 ∨ i = 1) :
    (lentCD' l).any (fun x => decide (x.pos = .bind 0 i) && (pathKey x.path).isEmpty) = true := by
  rcases hl with rfl | rfl <;> rcases hi with rfl | rfl <;> decide +kernel

/-- **The conditional dependence.** -/
theorem dws_CD (X Y R J M : SBinding) (c : Nat) (g : Sem → Sem → Sem) (vj vm : Sem) :
    DepWithinSites dm Γ (SCD X Y R J M c g vj vm) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f
    · rcases i with _ | _ | i
      · have h1 := agree_of_rootSited h (l := 1) (rs_CD 1 (.inl rfl) 0 (.inl rfl))
        have h2 := agree_of_rootSited h (l := 2) (rs_CD 2 (.inr rfl) 0 (.inl rfl))
        simp only [SState.valAt, SCD]
        show fx 1 2 c ψ = fx 1 2 c ψ'
        unfold fx; rw [h1, h2]
      · have h1 := agree_of_rootSited h (l := 1) (rs_CD 1 (.inl rfl) 1 (.inr rfl))
        have h2 := agree_of_rootSited h (l := 2) (rs_CD 2 (.inr rfl) 1 (.inr rfl))
        simp [SState.valAt, SCD, h1, h2]
      · rcases i with _ | _ | _ | i <;> simp [SState.valAt, SCD]
    · simp [SState.valAt, SCD]
  · rcases f with _ | f <;> simp [SState.valAt, SCD]

/-! ## The first site below a root: a reborrow through `*` -/

/-- The reference's state after `let r = σ1(&c1); let s = &*r` (the attack's program, `Attack.S₄`
then the borrow, `s`'s borrow `k+2` still parked in temporary `2`): `r` reads `k+2`'s final
content, lent at `(r, [*])`. -/
noncomputable def SRb (F : Attack.GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) : SState :=
  { env := [{ binds := [{ b with val := fun φ' => match (φ' (k+1)).as Nat with
                                                  | some x => .el0 Nat ((F n).val.2 x).2
                                                  | none => .err },
                        { ty := ⟨TyM.nat, some (k+1)⟩, val := fun φ' => φ' (k+2) }],
              temps := [fun φ' => match (φ' (k+1)).as Nat with | some _ => .moved | none => .moved,
                        fun _ => .moved, fun _ => .el0 Nat (F n).val.1] }],
    shape := fun p => if p = .temp 0 2 then some (k+2) else if p = .bind 0 1 then some (k+1) else none,
    nextLoan := k + 3,
    lent := fun m => if m = k + 2 then [⟨.bind 0 1, [.deref], false⟩] else Attack.lentA k m,
    heldTy := fun m => if m = k + 2 then TyM.nat else if m = k + 1 then TyM.nat else if m = k then b.ty.m else TyM.err,
    heldMem := fun m => if m = k + 2 then .el0 Nat (F n).val.1 else if m = k + 1 then .el0 Nat (F n).val.1
      else if m = k then c else .err }

set_option maxHeartbeats 1000000 in
/-- `&*r` on `S₄`, by the reference's own `borrowPlace`. -/
theorem borrowPlace_deref_S₄ (K : RunCtx) (φ : Future) (F : Attack.GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    borrowPlace K φ (.deref (.var 0)) (Attack.S₄ F n b k c)
      = some ((.el0 Nat (F n).val.1, ⟨TyM.nat, some (k+2)⟩), SRb F n b k c) := by
  simp only [borrowPlace, Attack.contentOf_deref_r, bind, Option.bind]
  simp [Sem.whole, SState.freshLoan, SState.pushTempShaped, SState.pushTemp, SState.setAt, SState.topIdx,
    SState.tyAt, SState.valAt, Attack.updAt_deref, Attack.updAt_nil, SState.setLent, SState.setHeldTy, SState.setHeldMem, Attack.S₄, SRb,
    List.modify, List.modifyTailIdx, List.modifyTailIdx.go, List.modifyHead]
  and_intros
  all_goals first
    | rfl
    | (funext φ'; cases Sem.as Nat (φ' (k+1)) <;> rfl)

/-- `s`'s borrow `k+2` is live: temporary `2` holds it. -/
theorem live_SRb (F : Attack.GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) : (SRb F n b k c).Live (k+2) := by
  rw [SState.live_iff]
  exact ⟨.temp 0 2, by simp [SRb, SState.positions, List.range'], by simp [SRb]⟩

/-- **The reborrow's lender**: `r` reads `s`'s borrow `k+2`, lent at `(r, [*])`, whose key is the
root's, so every path at `r` is comparable with it. -/
theorem dws_SRb (F : Attack.GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    DepWithinSites dm Γ (SRb F n b k c) := by
  apply dws_of_root
  intro p ψ ψ' h
  rcases p with ⟨f, i⟩ | ⟨f, i⟩
  · rcases f with _ | f
    · rcases i with _ | _ | i
      · have := agree_of_rootSited h (l := k+1) (by simp [rootSited, SRb, Attack.lentA, pathKey])
        simp [SState.valAt, SRb, this]
      · have := agree_of_rootSited h (l := k+2) (by simp [rootSited, SRb, pathKey, Step.key])
        simp [SState.valAt, SRb, this]
      · simp [SState.valAt, SRb]
    · simp [SState.valAt, SRb]
  · rcases f with _ | f
    · rcases i with _ | _ | _ | i
      · simp only [SState.valAt, SRb]
        show (match Sem.as Nat (ψ (k+1)) with | some _ => Sem.moved | none => Sem.moved)
          = (match Sem.as Nat (ψ' (k+1)) with | some _ => Sem.moved | none => Sem.moved)
        split <;> split <;> rfl
      all_goals simp [SState.valAt, SRb]
    · simp [SState.valAt, SRb]

/-! ### The record: with the positional comparison it failed -/

/-- Sites compared step by step, `*` included (the comparison before D67's erasure). -/
def walkHit (steps ψ : List Step) : Bool :=
  (walkKey ψ).isPrefixOf (walkKey steps) || (walkKey steps).isPrefixOf (walkKey ψ)

def DepWithinSitesW (s : SState) : Prop :=
  ∀ (p : Pos) (steps : List Step) (ψ ψ' : Future),
    (∀ l, ψ l ≠ ψ' l → s.Live l ∧ s.reached p (walkHit steps) l = false) →
    Sem.follow dm Γ (s.tyAt p) (s.valAt p ψ) steps = Sem.follow dm Γ (s.tyAt p) (s.valAt p ψ') steps

/-- **With the positional comparison the invariant failed at the reborrow's lender, at a path that
skips the `*`**: `r` read at `[.0]` is `k+2`'s final content's predecessor, so two typed futures
differing only at `k+2` (`1`, `2`) read `0` and `1`; `[.0]` and `[*]` are incomparable step by
step. -/
theorem dwsW_fails_SRb (F : Attack.GCar) (n : Nat) (b : SBinding) (k : Nat) (c : Sem) :
    ¬ DepWithinSitesW dm Γ (SRb F n b k c) := by
  intro h
  have := h (.bind 0 1) [.proj 0] (fun l => if l = k+2 then .el0 Nat 1 else .err)
    (fun l => if l = k+2 then .el0 Nat 2 else .err) (fun l hl => ?_)
  · simp [SRb, SState.valAt, Sem.follow, Sem.step, Sem.asNat_el0] at this
  · by_cases hlk : l = k + 2
    · subst hlk
      exact ⟨live_SRb F n b k c, by simp [SState.reached, SRb, walkHit, walkKey, Step.key, List.isPrefixOf]⟩
    · simp [hlk] at hl

end Ochr.Meaning.Regress.DepSites
