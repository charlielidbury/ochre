import Ochr.Meaning.Steps.FrameInduction
import Ochr.Meaning.Steps.FrameRec

/-!
# The call in place, from the frame property: the first use (lead36, 2026-11-27; docs/31 D230)

Corollary C1 of `<sec-frame-stmt>` ("a call in place"; Lean `callOf_inPlace`, open), for a GLOBAL callee whose body is
in the fragment the frame property is proved on (`Term.frameFree`: no function, function type or `Id` formed in it).
Two runs of the callee's body:
- IN PLACE (`CallRef.runCallRef`, the checker's `runBody`): its frame pushed on the caller's state (`callFrame`: `self`
  the callee's meaning at its declared type, each parameter the argument, a borrow parameter holding the ARGUMENT's
  label `kᵢ`), the body, the pop (`popCallFrame`);
- IN THE CLOSURE (`RunCongr.fixBodyAt`, the `.fix` clause's `bodyAt`): from the global's forming state `stateOf 0 []`
  under a fresh bottom frame, `self`, then each parameter (`fixStep`: a borrow parameter at a FRESH label `lᵢ = i` with a
  cell in frame 0), the body, the ends of every label but the returned one, the cells read as the finals.
`callOf` applies the closure's function `G` (`fixG`), which the fixpoint equation (`FixEqG`) equates with the closure run
whose `self` is `G` itself at its true type.

**What is proved here** (`body_agree`): from the start condition `CallStartG` (the in-place state after the push and the
closure's state after its parameters are pushed are related by the internal relation `FrameInv` under the call's renaming
`callRen`, and the call point meets `FrameStart`), the two body runs agree (`FrameAgreeI`): the frame property
`runFrameI_frameFree` APPLIES at the call, with the in-place state after the push as its `s₀` (the fourth referee's F3: its
`s₀` is that state, not the call point), the parameter labels `ks` the arguments' labels in parameter order, and the
closure's side `fixBodyAt`'s. And C1 (`callInPlace_of`): `runCallRef` and `callOf` of a global's meaning agree (both fail,
or the same result and a state to which the relation transfers), from `CallStartG`, the pop and link `CallPopG`, and the
fixpoint equation `FixEqG`.

**The gap the first use found (docs/31 D230), closed**: as first written `runBodyRef` read the callee's parameter types,
codomain and codomain reading on the CALLER's state with the capture frame pushed, the closure on its forming state: the
frame property's start (`FrameRel.top`, the parameters' stored types; the hint the body runs at) needs them EQUAL, which
held only through a frame-independence of type runs nothing stated (a type with an `Id` observes every position; one
formed in a body would read the caller's frames under the strict whole-state test). Repaired by reading them in the
closure value's own forming state (`CallRef.runBodyRef`, `Statements.bodyFrame`), as the paper's C4 says ("equal by
definition").
-/

namespace Ochr.Meaning.Steps.Form.CallInPlace

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.Steps.Form Ochr.Meaning.Steps.Form.FrameEnd

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- The in-place state after the push (`runBodyRef`'s, at a global: no captures). -/
noncomputable def inStart (fres : Res) (ds : List Term) (c : Term) (args : List Res) (s : SState) : SState :=
  callFrame K ρ φ [] [] fres (fbG K ρ φ ds c).2.2 (fbG K ρ φ ds c).1 args s

/-- The closure's state after the push (`fixBodyAt`'s `s₂`), at `self` meaning `selfM` at `piT`. -/
noncomputable def clStart (ds : List Term) (c : Term) (piT : TyM) (selfM : Sem) (args : List Sem) : SState :=
  ((args.zip (psG K ρ φ ds)).foldl (fixStep (fbG K ρ φ ds c))
    ((formG.under.pushBind { ty := .plain piT, val := fun _ => selfM, decl := .pi (fbG K ρ φ ds c).2.2 }), [], [])).1

end

/-- The parameter labels of a call: the labels its arguments carry, in parameter order (each a borrow argument's). -/
def argLabels (args : List Res) : List Nat := args.filterMap (·.2.label)

/-- **The call's renaming** of the closure's labels to the in-place ones: the cells' labels `0, …, m - 1` (fresh from the
forming state's counter `0`, in parameter order) to the parameter labels, the closure's later labels to the in-place
counter onwards. -/
def callRen (ks : List Nat) (n : Nat) (l : Nat) : Nat :=
  if h : l < ks.length then ks[l] else n + (l - ks.length)

/-! ## The call's renaming: the clauses of `FrameRel` and `FrameInv` that hold by its definition -/

theorem callRen_lt {ks : List Nat} {n l : Nat} (h : l < ks.length) : callRen ks n l = ks[l] := by
  simp [callRen, h]

theorem callRen_ge {ks : List Nat} {n l : Nat} (h : ks.length ≤ l) : callRen ks n l = n + (l - ks.length) := by
  simp [callRen, Nat.not_lt.2 h]

/-- `FrameRel.fresh` at the start: the closure's counter is `ks.length` (one cell per parameter label). -/
theorem callRen_fresh (ks : List Nat) (n j : Nat) : callRen ks n (ks.length + j) = n + j := by
  rw [callRen_ge (Nat.le_add_right _ _)]; congr 1; omega

/-- `FrameInv.srange`: every closure label goes to a parameter label or to one at or above the call's counter. -/
theorem callRen_srange (ks : List Nat) (n l : Nat) : callRen ks n l ∈ ks ∨ n ≤ callRen ks n l := by
  by_cases h : l < ks.length
  · exact .inl (by rw [callRen_lt h]; exact List.getElem_mem h)
  · exact .inr (by rw [callRen_ge (Nat.le_of_not_lt h)]; omega)

/-- `FrameRel.inj`: one to one, the parameter labels being distinct and below the call's counter. -/
theorem callRen_inj {ks : List Nat} {n : Nat} (hnd : ks.Nodup) (hlt : ∀ k ∈ ks, k < n) (l l' : Nat)
    (h : callRen ks n l = callRen ks n l') : l = l' := by
  by_cases h₁ : l < ks.length <;> by_cases h₂ : l' < ks.length
  · rw [callRen_lt h₁, callRen_lt h₂] at h
    exact (List.getElem_inj hnd).mp h
  · rw [callRen_lt h₁, callRen_ge (Nat.le_of_not_lt h₂)] at h
    have := hlt _ (List.getElem_mem h₁); omega
  · rw [callRen_ge (Nat.le_of_not_lt h₁), callRen_lt h₂] at h
    have := hlt _ (List.getElem_mem h₂); omega
  · rw [callRen_ge (Nat.le_of_not_lt h₁), callRen_ge (Nat.le_of_not_lt h₂)] at h; omega

/-- `AccInv.order`/`orderAll` and `mono`/`monoAll`: the parameter labels' preimages are the first, and the renaming is
monotone on the others. -/
theorem callRen_order {ks : List Nat} {n : Nat} (hlt : ∀ k ∈ ks, k < n) (l l' : Nat)
    (h : callRen ks n l ∈ ks) (h' : callRen ks n l' ∉ ks) : l < l' := by
  by_cases h₁ : l < ks.length
  · by_cases h₂ : l' < ks.length
    · exact absurd (by rw [callRen_lt h₂]; exact List.getElem_mem h₂) h'
    · omega
  · rw [callRen_ge (Nat.le_of_not_lt h₁)] at h
    have := hlt _ h; omega

theorem callRen_mono {ks : List Nat} {n : Nat} (l l' : Nat) (h : callRen ks n l ∉ ks) (h' : callRen ks n l' ∉ ks)
    (hl : l < l') : callRen ks n l < callRen ks n l' := by
  have h₁ : ks.length ≤ l := Nat.le_of_not_lt fun hlt => h (by rw [callRen_lt hlt]; exact List.getElem_mem hlt)
  have h₂ : ks.length ≤ l' := Nat.le_of_not_lt fun hlt => h' (by rw [callRen_lt hlt]; exact List.getElem_mem hlt)
  rw [callRen_ge h₁, callRen_ge h₂]; omega

/-- The push reads the callee's meaning and its type's code only (`self` is bound at `{fres.2 with label := none}`):
`K.C.global g` and `(selfG, .plain piTG)` push the same frame where they agree there. -/
theorem inStart_fres (K : RunCtx) (ρ : Assignment) (φ : Future) {fres fres' : Res} (h1 : fres.1 = fres'.1)
    (h2 : fres.2.m = fres'.2.m) (ds : List Term) (c : Term) (args : List Res) (s : SState) :
    inStart K ρ φ fres ds c args s = inStart K ρ φ fres' ds c args s := by
  obtain ⟨a, ⟨m, l⟩⟩ := fres
  obtain ⟨a', ⟨m', l'⟩⟩ := fres'
  simp only at h1 h2
  subst h1 h2
  rfl

/-! ## The start, `FrameStart`'s half: proved (docs/31 D230) -/

namespace PushFrame

open SState

theorem lookup_pushFrame (s : SState) (p : Pos) : s.pushFrame.lookup p = s.lookup p := by
  have e : s.pushFrame.env = s.env ++ [({} : SFrame)] := rfl
  cases p with
  | bind f i =>
    simp only [lookup, e]
    by_cases h : f < s.env.length
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right (Nat.le_of_not_lt h), List.getElem?_eq_none (Nat.le_of_not_lt h)]
      cases f - s.env.length <;> simp
  | temp f i =>
    simp only [lookup, e]
    by_cases h : f < s.env.length
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right (Nat.le_of_not_lt h), List.getElem?_eq_none (Nat.le_of_not_lt h)]
      cases f - s.env.length <;> simp

theorem valAt_pushFrame (s : SState) : s.pushFrame.valAt = s.valAt := by
  funext p; rw [valAt_eq, valAt_eq, lookup_pushFrame]

theorem mem_positions_pushFrame (s : SState) (p : Pos) : p ∈ s.pushFrame.positions ↔ p ∈ s.positions := by
  rw [mem_positions, mem_positions, lookup_pushFrame]

theorem live_pushFrame (s : SState) (l : Nat) : s.pushFrame.Live l ↔ s.Live l := by
  rw [live_iff, live_iff]; simp only [mem_positions_pushFrame]; rfl

theorem rinv_pushFrame {L : Nat → Prop} {s : SState} (h : RInv L s) : RInv L s.pushFrame := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun p => ?_, fun r x hr hx => ?_, fun p x hx => ?_⟩
  · rw [valAt_pushFrame]
    exact (h1 p).mono fun y hy => hy.elim .inl fun h => .inr ((live_pushFrame s y).2 h)
  · rw [valAt_pushFrame]
    rw [mem_positions_pushFrame] at hr
    exact (h2 r x hr hx).mono fun y hy => by
      simp only [live_pushFrame]; exact hy
  · obtain ⟨hp, hlt⟩ := h3 p x hx
    exact ⟨(mem_positions_pushFrame s p).2 hp, hlt⟩

end PushFrame

/-- The binding `callFrame` pushes for an argument, at the earlier arguments `acc`. -/
noncomputable def paramBind (bs : List PBind) (acc : List Sem) (a : Res) : SBinding :=
  { ty := { (match bs[acc.length]? with | some b => b.1 acc | none => TyS.plain TyM.err) with label := a.2.label },
    val := fun _ => a.1, decl := match bs[acc.length]? with | some b => b.2 | none => .other }

/-- `callFrame`'s step: one parameter pushed (`CallRef.callFrame`'s `step`). -/
noncomputable def callStep (bs : List PBind) (sa : SState × List Sem) (a : Res) : SState × List Sem :=
  (pushBindShaped sa.1 (paramBind bs sa.2 a), sa.2 ++ [a.1])

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

theorem inStart_eq (fres : Res) (ds : List Term) (c : Term) (args : List Res) (s : SState) :
    inStart K ρ φ fres ds c args s =
      (args.foldl (callStep (fbG K ρ φ ds c).1)
        (s.pushFrame.pushBind { ty := { fres.2 with label := none }, val := fun _ => fres.1, decl := .pi (fbG K ρ φ ds c).2.2 },
          [])).1 := by
  simp only [inStart, callFrame, capsState, capsVals, capsTys, List.zip_nil_left, List.map_nil, List.foldl_nil]
  rfl

end

/-- A push of a binding leaves the shape of a position below the top frame as it was, but at the holder of the label
the binding takes (cleared). -/
theorem shape_pushBindShaped_lower {t : SState} (b : SBinding) {q : Pos} (hq : q.frameOf < t.topIdx) :
    (pushBindShaped t b).shape q = match b.ty.label with
      | some l => if t.holderOf l = some q then none else t.shape q
      | none => t.shape q := by
  unfold pushBindShaped
  cases hl : b.ty.label with
  | none => rfl
  | some l =>
    dsimp only
    have hlow : (t.takeLabel l).shape q = if t.holderOf l = some q then none else t.shape q := by
      unfold SState.takeLabel
      cases hh : t.holderOf l with
      | none => simp
      | some r =>
        show (if q = r then none else t.shape q) = _
        by_cases e : q = r
        · subst e; simp
        · rw [if_neg e, if_neg (fun h => e (Option.some.inj h).symm)]
    split
    · rename_i fr hfr
      have hne : q ≠ .bind ((t.takeLabel l).pushBind b).topIdx (fr.binds.length - 1) := by
        intro e
        have ht : ((t.takeLabel l).pushBind b).topIdx = t.topIdx := by
          simp [SState.topIdx, SState.pushBind, SState.takeLabel]; split <;> simp [SState.setAt] <;> split <;> simp
        rw [e, ht] at hq; simp [Pos.frameOf] at hq
      have e : (if q = Pos.bind ((t.takeLabel l).pushBind b).topIdx (fr.binds.length - 1) then some l
          else ((t.takeLabel l).pushBind b).shape q) = (t.takeLabel l).shape q := by rw [if_neg hne]; rfl
      simp only [e]
      exact hlow
    · exact hlow

theorem env_length_pushBindShaped (t : SState) (b : SBinding) : (pushBindShaped t b).env.length = t.env.length := by
  unfold pushBindShaped
  have h1 : ∀ u : SState, (u.pushBind b).env.length = u.env.length := fun u => by simp [SState.pushBind]
  have h2 : ∀ l, (t.takeLabel l).env.length = t.env.length := fun l => by
    unfold SState.takeLabel; split
    · rename_i r _; cases r <;> simp [SState.setAt]
    · rfl
  cases b.ty.label with
  | none => exact h1 t
  | some l => dsimp only; split <;> simp [h1, h2]

theorem lent_pushBindShaped (t : SState) (b : SBinding) : (pushBindShaped t b).lent = t.lent := by
  unfold pushBindShaped
  have h1 : ∀ u : SState, (u.pushBind b).lent = u.lent := fun _ => rfl
  cases b.ty.label with
  | none => rfl
  | some l =>
    have h2 : (t.takeLabel l).lent = t.lent := by
      unfold SState.takeLabel; split
      · rename_i r _; cases r <;> rfl
      · rfl
    dsimp only; split <;> simp [h1, h2]

/-- **The fold of `callFrame`'s steps**: from the state after `self`'s push, locality, unique holders, the frames, the
counter, the sites and the call point's live labels are kept, and a position of the call point's frames holds a label
only if it held it at the call point and the label was not taken by a parameter. -/
theorem fold_start (bs : List PBind) (s : SState) :
    ∀ (args : List Res) (t : SState) (acc : List Sem) (done : List Nat),
    SState.RInv (fun _ => False) t → t.Uniq → t.env.length = s.env.length + 1 → t.nextLoan = s.nextLoan →
    t.lent = s.lent → (∀ l, s.Live l → t.Live l) →
    (∀ p l, p.frameOf < s.env.length → t.shape p = some l → s.shape p = some l ∧ l ∉ done) →
    (∀ a ∈ args, ∀ l, a.2.label = some l → s.Live l) →
    SState.RInv (fun _ => False) (args.foldl (callStep bs) (t, acc)).1 ∧ (args.foldl (callStep bs) (t, acc)).1.Uniq ∧
      (args.foldl (callStep bs) (t, acc)).1.env.length = s.env.length + 1 ∧
      (args.foldl (callStep bs) (t, acc)).1.nextLoan = s.nextLoan ∧ (args.foldl (callStep bs) (t, acc)).1.lent = s.lent ∧
      (∀ l, s.Live l → (args.foldl (callStep bs) (t, acc)).1.Live l) ∧
      (∀ p l, p.frameOf < s.env.length → (args.foldl (callStep bs) (t, acc)).1.shape p = some l →
        s.shape p = some l ∧ l ∉ done ++ args.filterMap (·.2.label))
  | [], t, acc, done, hr, hu, hlen, hn, hlent, hlive, hsh, _ => by
    simpa using ⟨hr, hu, hlen, hn, hlent, hlive, hsh⟩
  | a :: rest, t, acc, done, hr, hu, hlen, hn, hlent, hlive, hsh, hargs => by
    simp only [List.foldl_cons]
    have hstep : callStep bs (t, acc) a = (pushBindShaped t (paramBind bs acc a), acc ++ [a.1]) := rfl
    rw [hstep]
    generalize hb : paramBind bs acc a = b
    have hsa := hr.2.2
    have htop : t.topIdx = s.env.length := by simp [SState.topIdx, hlen]
    have hlab : b.ty.label = a.2.label := by rw [← hb]; rfl
    have hbv : b.val = fun _ => a.1 := by rw [← hb]; rfl
    -- the label the step takes is live in `t`, below the counter
    have hkl : ∀ k, a.2.label = some k → t.Live k ∧ k < t.nextLoan := fun k hk => by
      have hk' := hlive k (hargs a (List.mem_cons_self ..) k hk)
      obtain ⟨q, _, hq⟩ := (SState.live_iff t k).1 hk'
      exact ⟨hk', (hsa q k hq).2⟩
    have hr' : SState.RInv (fun _ => False) (pushBindShaped t b) :=
      SState.pushBindShaped_rinv hr b a.1 hbv fun l hl => by
        rw [hlab] at hl; obtain ⟨h1, h2⟩ := hkl l hl; exact ⟨.inl h1, h2⟩
    have hne : t.env ≠ [] := by intro e; rw [e] at hlen; simp at hlen
    have ih := fold_start bs s rest (pushBindShaped t b) (acc ++ [a.1]) (done ++ a.2.label.toList) hr'
      (hu.pushBindShaped hsa b) (by rw [env_length_pushBindShaped, hlen]) (by rw [nextLoan_pushBindShaped, hn])
      (by rw [lent_pushBindShaped, hlent])
      (fun l hl => (live_pushBindShaped hsa b hne l).2 (.inl (hlive l hl)))
      (fun p l hp hl => by
        have hp' : p.frameOf < t.topIdx := by rw [htop]; exact hp
        rw [shape_pushBindShaped_lower b hp', hlab] at hl
        cases hk : a.2.label with
        | none =>
          rw [hk] at hl
          obtain ⟨h1, h2⟩ := hsh p l hp hl
          exact ⟨h1, by simpa [hk] using h2⟩
        | some k =>
          rw [hk] at hl
          dsimp only at hl
          split at hl
          · cases hl
          · rename_i hnh
            obtain ⟨h1, h2⟩ := hsh p l hp hl
            refine ⟨h1, ?_⟩
            simp only [Option.toList_some, List.mem_append, List.mem_singleton, not_or]
            refine ⟨h2, fun hlk => ?_⟩
            subst hlk
            obtain ⟨r, hr₀⟩ := SState.holderOf_of_live (hkl l hk).1
            have := hu p r l hl (SState.holderOf_spec hr₀).2
            subst this
            exact hnh hr₀)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := ih
    refine ⟨i1, i2, i3, i4, i5, i6, fun p l hp hl => ?_⟩
    obtain ⟨h1, h2⟩ := i7 p l hp hl
    refine ⟨h1, ?_⟩
    cases hk : a.2.label <;> simpa [hk, List.filterMap_cons] using h2

/-- A position lies in an existing frame. -/
theorem frameOf_lt_of_mem {s : SState} {p : Pos} (hp : p ∈ s.positions) : p.frameOf < s.env.length := by
  rw [SState.mem_positions] at hp
  cases p with
  | bind f i =>
    simp only [SState.lookup] at hp
    cases h : s.env[f]? with
    | none => rw [h] at hp; simp at hp
    | some _ => exact (List.getElem?_eq_some_iff.1 h).1
  | temp f i =>
    simp only [SState.lookup] at hp
    cases h : s.env[f]? with
    | none => rw [h] at hp; simp at hp
    | some _ => exact (List.getElem?_eq_some_iff.1 h).1

/-- **`FrameStart` at the in-place state after the push** (PROVED; the half of `CallStartG` that is about the call point):
from locality at the call point (every position reads only live labels, `RInv`), unique holders, every site at a
position, and the arguments' labels live and distinct. The push binds `self` and the parameters in a new frame, takes
each argument's label from its holder in the caller's frames, and touches no site and no counter. -/
theorem frameStart_inStart (K : RunCtx) (ρ : Assignment) (φ : Future) (fres : Res) (ds : List Term) (c : Term)
    (args : List Res) (s : SState) (hloc : SState.RInv (fun _ => False) s) (hu : s.Uniq)
    (hsites : ∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions)
    (hlive : ∀ a ∈ args, ∀ l, a.2.label = some l → s.Live l) (hnd : (argLabels args).Nodup) :
    FrameStart (inStart K ρ φ fres ds c args s) (argLabels args) := by
  rw [inStart_eq]
  generalize hb₀ : ({ ty := { fres.2 with label := none }, val := fun _ => fres.1, decl := .pi (fbG K ρ φ ds c).2.2 } :
    SBinding) = b₀
  have hsa := hloc.2.2
  have hb₀v : b₀.val = fun _ => fres.1 := by rw [← hb₀]
  have ht₀r : SState.RInv (fun _ => False) (s.pushFrame.pushBind b₀) :=
    SState.pushBind_rinv (PushFrame.rinv_pushFrame hloc) b₀ fres.1 hb₀v
  have hsa₀ : SState.ShapeAt s.pushFrame := (PushFrame.rinv_pushFrame hloc).2.2
  obtain ⟨_, _, hlen, hn, hlent, _, hsh⟩ := fold_start (fbG K ρ φ ds c).1 s args (s.pushFrame.pushBind b₀) [] []
    ht₀r (hu.pushBind b₀) (by simp [SState.pushBind, SState.pushFrame]) rfl rfl
    (fun l hl => (SState.live_pushBind hsa₀ b₀ l).2 ((PushFrame.live_pushFrame s l).2 hl))
    (fun p l _ hl => ⟨hl, by simp⟩) hlive
  have hrinv := (fold_start (fbG K ρ φ ds c).1 s args (s.pushFrame.pushBind b₀) [] [] ht₀r (hu.pushBind b₀)
    (by simp [SState.pushBind, SState.pushFrame]) rfl rfl
    (fun l hl => (SState.live_pushBind hsa₀ b₀ l).2 ((PushFrame.live_pushFrame s l).2 hl))
    (fun p l _ hl => ⟨hl, by simp⟩) hlive).1
  generalize (args.foldl (callStep (fbG K ρ φ ds c).1) (s.pushFrame.pushBind b₀, [])).1 = t at hlen hn hlent hsh hrinv
  have htop : t.topIdx = s.env.length := by simp [SState.topIdx, hlen]
  -- a live label is below the counter
  have hlt : ∀ u : SState, SState.ShapeAt u → ∀ l, u.Live l → l < u.nextLoan := fun u hsu l hl => by
    obtain ⟨q, _, hq⟩ := (SState.live_iff u l).1 hl
    exact (hsu q l hq).2
  -- an argument's label is live at the call point
  have hks : ∀ k ∈ argLabels args, s.Live k := fun k hk => by
    obtain ⟨a, ha, hak⟩ := List.mem_filterMap.1 hk
    exact hlive a ha k hak
  refine ⟨fun p _ ψ ψ' hψ => ?_, fun k hk => ?_, fun p l hp hl => ?_, fun p l x hp hl hx => ?_, hnd⟩
  · exact hrinv.1 p ψ ψ' fun y hy => hψ y (hlt t hrinv.2.2 y (hy.elim False.elim id))
  · rw [hn]; exact hlt s hsa k (hks k hk)
  · rw [htop] at hp
    obtain ⟨h1, h2⟩ := hsh p l hp hl
    refine ⟨fun hm => h2 (by simpa [argLabels] using hm), ?_⟩
    rw [hn]; exact (hsa p l h1).2
  · rw [htop] at hp ⊢
    rw [hlent] at hx
    exact frameOf_lt_of_mem (hsites l x hx)

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **Each borrow argument's label is recorded at its parameter's content type** (docs/31 D240): the binder's type at the
earlier arguments, as the callee's frame stores it (`paramBind`) and as the closure records its cell's label (`fixStep`).
It replaces the start's `BorrowArgsTyped`, which reads the content types off the function type's telescope CODE
(`refTysOf`): the two agree only through a round trip of codes (each domain fitting the type's level and canonical,
the knot's `PiCallable`), and at a function of sort `Prop` (`piTyAt 0`, a proposition) `refTysOf` is empty, so
`BorrowArgsTyped` constrains nothing and `CallStartInvG` as first stated was false there (the caller's record of a
borrow argument's label is free, the closure's is the binder's); no in-place call of such a function is made (a proof
call never runs its body), so nothing used the false case. -/
def ArgsHeld (ds : List Term) (c : Term) (args : List Res) (s : SState) : Prop :=
  ∀ (j : Nat) (a : Res) (k : Nat), args[j]? = some a → a.2.label = some k →
    s.heldTy k = (paramBind (fbG K ρ φ ds c).1 ((args.take j).map (·.1)) a).ty.m

/-- **The start of a call in place** (MODEL; PROVED, `CallStartInv.callStartG`; the paper's start lemma, `<sec-frame-fix>`). At a call point `s` of a
global's code, with arguments `args` that are members of the domains, carrying labels exactly at the borrow parameters
(held at their parameters' content types: `ArgsHeld`, docs/31 D240), and the callee's meaning `fres = (selfM, piT)` a member of
its type: the in-place state after the push is a call point for the frame property (`FrameStart`, with itself as `s₀`) and
is related to the closure's state after its push by the internal relation, under `callRen`. Hypotheses on the call point
beyond goodness: locality (every position reads only live labels, `SState.RInv (fun _ => False)`, which the run keeps,
`runT_rinv`; `SGood` gives only the POINTWISE `ReadsBelow`, which does not give `FrameStart.reads`, docs/31 D230), lending well founded (`LendWF`, the paper's (H6), from the checker's acyclic lending through (II)'s
relation), and every site at a position (so the fresh frame holds no site). Read clause by clause against `FrameInv`
(docs/31 D230): every clause holds at the start by the push's construction (the two top frames are `self` and the
parameters, the same meanings, types and readings, the labels `kᵢ` against `lᵢ = i`; frame 0 of the closure is the
cells, each reading its own label, lent there; the caller's frames are `s₀`'s own, read at `cellFuture`, the identity at
the start), with `ArgsHeld` giving the held types (`FrameRel.held`, `heldAll`), the domains' membership the
goodness of both states, and `callRen` the range, order and counter clauses by its definition. -/
def CallStartG : Prop :=
  ∀ (hs : List Hint) (ds : List Term) (c : Term) (selfM : Sem) (piT : TyM) (args : List Res) (s : SState),
    piT = piTyAt K.dm.read (K.D.piSort (scopeOf formG) (.pi hs ds c)) (psG K ρ φ ds) (outG K ρ φ ds c) →
    selfM ∈ₛ[K.dm.read] piT →
    Strict.SGood K.dm K.Γ φ s → SState.RInv (fun _ => False) s → LendWF s →
    (∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions) →
    (∀ a ∈ args, ∀ l, a.2.label = some l → s.Live l) → (argLabels args).Nodup →
    DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)) →
    (∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef)) →
    ArgsHeld K ρ φ ds c args s →
    FrameStart (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args) ∧
    FrameInv K φ (callRen (argLabels args) s.nextLoan) (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args)
      (inStart K ρ φ (selfM, .plain piT) ds c args s) (clStart K ρ φ ds c piT selfM (args.map (·.1)))

/-- **The start of a call in place, its internal relation** (MODEL; PROVED, `CallStartInv.callStartInvG`, docs/31 D240): `CallStartG`'s `FrameInv` half, at the same
hypotheses; its `FrameStart` half is proved (`frameStart_inStart`). -/
def CallStartInvG : Prop :=
  ∀ (hs : List Hint) (ds : List Term) (c : Term) (selfM : Sem) (piT : TyM) (args : List Res) (s : SState),
    piT = piTyAt K.dm.read (K.D.piSort (scopeOf formG) (.pi hs ds c)) (psG K ρ φ ds) (outG K ρ φ ds c) →
    selfM ∈ₛ[K.dm.read] piT →
    Strict.SGood K.dm K.Γ φ s → SState.RInv (fun _ => False) s → LendWF s →
    (∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions) →
    (∀ a ∈ args, ∀ l, a.2.label = some l → s.Live l) → (argLabels args).Nodup →
    DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)) →
    (∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef)) →
    ArgsHeld K ρ φ ds c args s →
    FrameInv K φ (callRen (argLabels args) s.nextLoan) (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args)
      (inStart K ρ φ (selfM, .plain piT) ds c args s) (clStart K ρ φ ds c piT selfM (args.map (·.1)))

/-- `CallStartG` from its `FrameInv` half: the `FrameStart` half is `frameStart_inStart`. -/
theorem callStartG_of (h : CallStartInvG K ρ φ) : CallStartG K ρ φ :=
  fun hs ds c selfM piT args s hpi hself hg hloc hl hsites hlive hnd hdom hlab hbt =>
    ⟨frameStart_inStart K ρ φ _ ds c args s hloc hg.uniq hsites hlive hnd,
      h hs ds c selfM piT args s hpi hself hg hloc hl hsites hlive hnd hdom hlab hbt⟩

/-- **The first use of the frame property** (PROVED from `CallStartG`): at a call of a global whose body is frame-free, the
body's run in place (from the pushed frame) and its run in the closure (from the closure's pushed frame), at the same
hint, both fail or agree: the same result, its label renamed by `callRen`, the internal relation at the end. -/
theorem body_agree (hst : CallStartG K ρ φ) (hc : Strict.FundCtx K) (hs : List Hint) (ds : List Term) (c : Term)
    (body : Term) (hv : body.valsOk (Strict.ValsP K ρ φ)) (hf : body.frameFree = true) (selfM : Sem) (piT : TyM)
    (args : List Res) (s : SState) (hint : TyS)
    (hpi : piT = piTyAt K.dm.read (K.D.piSort (scopeOf formG) (.pi hs ds c)) (psG K ρ φ ds) (outG K ρ φ ds c))
    (hself : selfM ∈ₛ[K.dm.read] piT) (hg : Strict.SGood K.dm K.Γ φ s) (hloc : SState.RInv (fun _ => False) s) (hl : LendWF s)
    (hsites : ∀ l (y : Site), y ∈ s.lent l → y.pos ∈ s.positions)
    (hlive : ∀ a ∈ args, ∀ l, a.2.label = some l → s.Live l) (hnd : (argLabels args).Nodup)
    (hdom : DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)))
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef))
    (hbt : ArgsHeld K ρ φ ds c args s) :
    FrameAgreeI K φ (callRen (argLabels args) s.nextLoan) (inStart K ρ φ (selfM, .plain piT) ds c args s) (argLabels args)
      (runT K ρ φ true hint body (inStart K ρ φ (selfM, .plain piT) ds c args s))
      (runT K ρ φ true hint body (clStart K ρ φ ds c piT selfM (args.map (·.1)))) := by
  obtain ⟨hs₀, hI⟩ := hst hs ds c selfM piT args s hpi hself hg hloc hl hsites hlive hnd hdom hlab hbt
  exact runFrameI_frameFree K ρ φ _ _ _ true hint body _ _ hc hs₀ hv hf hI

/-- The state the body's run in place starts from, before the push (`runCallRef`): at a borrow codomain the call first
reserves the result's label and lends it, as fills, wherever the borrow arguments are lent ([Lend], main's D99). -/
noncomputable def callPre (c : Term) (args : List Res) (s : SState) : SState :=
  match c with
  | .ref _ =>
    let lentK := ((args.filterMap (·.2.label)).flatMap s.lent).map fun x : Site => { x with fill := true }
    (s.freshLoan.2).setLent s.freshLoan.1 lentK
  | _ => s

/-- **Two outcomes of a call agree**: both fail, or both succeed with the same result, and the relation of a checker
state with the first state holds with the second (the counters, and the records and sites of dead labels, may differ:
the run in place made and ended the body's labels; `callOf` made none). The conclusion `Steps/Call.callOf_inPlace` asked,
for a checker state in which every label that occurs is live (the checker's (WF2) outside a sealed program's run). Without
that hypothesis the transfer is false by reading: `Rel.fresh` asks each occurring label's image below the reference's
counter, which is the body's labels' larger in place, and a stale loan of the checker's could be renamed to a dead label
the body made (docs/31 D230). -/
def InPlaceAgree : Option (Res × SState) → Option (Res × SState) → Prop
  | some (r, t), some (r', t') => r = r' ∧ ∀ (st : MState) (π : Nat → Nat),
      (∀ l, st.Occurs l → liveLoan st.env l = true) → Rel K ρ φ π st t → Rel K ρ φ π st t'
  | none, none => True
  | _, _ => False

/-- **The pop and the link** (MODEL; OPEN; the paper's pop lemma and the link to `callOf`, `<sec-frame-fix>`). At a call
of an accepted global (not the one under check) whose meaning is the closure of `G` at `piT` (`GlobalsOk.fn`), from
the agreement of the two body runs (`body_agree`) and the fixpoint equation at the arguments (`FixEqG`): the call in place
and `callOf` agree. Its parts, read (docs/31 D230): the pop's ends (`popEnds` from the in-place counter at the push, or
held in the callee's frame, but the returned label) are the closure's (every live label but the returned one) through
the renaming, in orders that differ only among parameter labels (`perm_fold`), their strict tests by (O1)
(`endOk_corr`, `frameRel_foldEnd`); after them the cells read the finals, and the caller's frames read the call point's at
the finals (`FrameRel.lowerVal`, `cellFuture` at constants), which is `callOf`'s `mapVals` with the fixes; the frame is
dropped, a returned borrow re-parked; at a borrow codomain the reserved label (the call point's counter) is `callOf`'s
fresh one, `endInto` its renaming; `callOf` applies `G` (`applyFnL_closureL`), which the fixpoint equation makes the
closure run the agreement is about. -/
def CallPopG : Prop :=
  ∀ (st : MState) (g : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat)
    (body : Term) (args : List Res) (s : SState),
    GlobalsOk K st → st.globals.find? (·.name == g) = some gd → K.cur.map (·.1) ≠ some g →
    gd.fn? = some (.fix self hs ds c dec body) →
    (K.C.global g).1 = selfG K ρ φ hs ds c dec body → (K.C.global g).2.m = piTG K ρ φ hs ds c →
    Strict.SGood K.dm K.Γ φ (callPre c args s) →
    DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)) →
    BorrowArgsTyped K.dm.read (K.C.global g) args s →
    GG K ρ φ hs ds c dec body (args.map (·.1)) = fixBodyAt K ρ φ (fbG K ρ φ ds c) formG (psG K ρ φ ds) (outG K ρ φ ds c)
      (piTG K ρ φ hs ds c) 0 body (selfG K ρ φ hs ds c dec body) (args.map (·.1)) →
    FrameAgreeI K φ (callRen (argLabels args) (callPre c args s).nextLoan)
      (inStart K ρ φ (selfG K ρ φ hs ds c dec body, .plain (piTG K ρ φ hs ds c)) ds c args (callPre c args s)) (argLabels args)
      (runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body
        (inStart K ρ φ (selfG K ρ φ hs ds c dec body, .plain (piTG K ρ φ hs ds c)) ds c args (callPre c args s)))
      (runT K ρ φ true ((fbG K ρ φ ds c).2.1 (args.map (·.1))) body
        (clStart K ρ φ ds c (piTG K ρ φ hs ds c) (selfG K ρ φ hs ds c dec body) (args.map (·.1)))) →
    InPlaceAgree K ρ φ (runCallRef K ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] args s)
      (callOf K.dm.read (K.C.global g) args s)

/-- `BorrowArgsTyped` reads the callee's type only. -/
theorem borrowArgsTyped_ty {fv fv' : Res} (h : fv.2.m = fv'.2.m) {args : List Res} {s : SState}
    (hb : BorrowArgsTyped K.dm.read fv args s) : BorrowArgsTyped K.dm.read fv' args s := by
  unfold BorrowArgsTyped refLabelsOf at hb ⊢
  rw [← h]; exact hb

/-- **C1, a call in place, for a frame-free body** (assembled; assumes `CallStartG`, `CallPopG`, and the context's fixpoint
clause `FixEqG`): at a call of an accepted global whose body is in the fragment the frame property is proved on, the call
run in place and `callOf` of the global's meaning agree. The frame property used is `runFrameI_frameFree`, proved. The
global's meaning is its closure at its forming state (`hselfV`, `hselfT`: what `GlobalsOk.fn` and the `.fix` clause give
where the global is a member, `hmem`). -/
theorem callInPlace_of (hst : CallStartG K ρ φ) (hpop : CallPopG K ρ φ) (hc : Strict.FundCtx K) (st : MState)
    (hfix : FixEqG K st) (hG : GlobalsOk K st) (g : String) (gd : GDef) (self : Hint) (hs : List Hint) (ds : List Term)
    (c : Term) (dec : Option Nat) (body : Term) (hfind : st.globals.find? (·.name == g) = some gd)
    (hcur : K.cur.map (·.1) ≠ some g) (hfn : gd.fn? = some (.fix self hs ds c dec body))
    (hv : body.valsOk (Strict.ValsP K ρ φ)) (hf : body.frameFree = true) (args : List Res) (s : SState)
    (hselfV : (K.C.global g).1 = selfG K ρ φ hs ds c dec body) (hselfT : (K.C.global g).2.m = piTG K ρ φ hs ds c)
    (hmem : (K.C.global g).1 ∈ₛ[K.dm.read] (K.C.global g).2.m)
    (hg : Strict.SGood K.dm K.Γ φ (callPre c args s)) (hloc : SState.RInv (fun _ => False) (callPre c args s))
    (hl : LendWF (callPre c args s))
    (hsites : ∀ l (y : Site), y ∈ (callPre c args s).lent l → y.pos ∈ (callPre c args s).positions)
    (hlive : ∀ a ∈ args, ∀ l, a.2.label = some l → (callPre c args s).Live l) (hnd : (argLabels args).Nodup)
    (hdom : DomMembers K.dm.read (psG K ρ φ ds) (args.map (·.1)))
    (hlab : ∀ (i : Nat) (a : Res) (d : PiDom), args[i]? = some a → (psG K ρ φ ds)[i]? = some d → (a.2.label.isSome = d.isRef))
    (hbt : BorrowArgsTyped K.dm.read (K.C.global g) args s)
    (hheld : ArgsHeld K ρ φ ds c args (callPre c args s)) :
    InPlaceAgree K ρ φ (runCallRef K ρ φ (K.C.global g) [] (.fix self hs ds c dec body) [] args s)
      (callOf K.dm.read (K.C.global g) args s) := by
  -- the fixpoint equation at the global's forming state, at the arguments
  have he := hfix g gd self hs ds c dec body hfind hcur hfn ρ φ (args.map fun a : Res => a.1)
    (hdom : DomMembers K.dm.read (runDoms K ρ φ formG ds) (args.map fun a : Res => a.1))
  -- the start, then the frame property at the body (`body_agree`)
  have hmem' : selfG K ρ φ hs ds c dec body ∈ₛ[K.dm.read] piTG K ρ φ hs ds c := by rw [← hselfV, ← hselfT]; exact hmem
  have hb := body_agree K ρ φ hst hc hs ds c body hv hf _ _ args (callPre c args s)
    ((fbG K ρ φ ds c).2.1 (args.map (·.1))) rfl hmem' hg hloc hl hsites hlive hnd hdom hlab hheld
  exact hpop st g gd self hs ds c dec body args s hG hfind hcur hfn hselfV hselfT hg hdom hbt he hb

end

end Ochr.Meaning.Steps.Form.CallInPlace
