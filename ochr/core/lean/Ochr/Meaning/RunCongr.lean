import Ochr.Meaning.RunPresInd

/-!
# Part (E) of the locality induction: the run at two futures

Two futures `φ`, `φ'` that agree on `L`; a state with `RInv L` (part (P), `RunPresInd.lean`). The
run reads the future only through [Access] (after which the accessed position factors through
`L`, `access_FT`), through the closed future (fixed at every live label, `closedFuture_read`),
after ending every borrow (`endAll_FT`), at a loan of the term (in `L`), and through a closure's
finals (`closureAt_congr`, with `FinalsIn` from the cells' order, `RunOrd.lean`). So the run at
`φ` is the run at `φ'`.

This file: the primitives. Each congruence holds at a state with `RInv L`.
-/

namespace Ochr.Meaning

open SState

section
variable (K : RunCtx) {φ φ' : Future} {L : Nat → Prop}

theorem contentOf_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    contentOf K φ p s = contentOf K φ' p s := by
  unfold contentOf
  cases resolve s p with
  | none => rfl
  | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    rw [access_FT hi.1 hi.2.1 pos φ φ' hφ]

theorem setContent_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (pos : Pos)
    (steps : List Step) (v : Sem) : setContent K φ pos steps v s = setContent K φ' pos steps v s := by
  unfold setContent
  dsimp only
  rw [closedFuture_read hi.1 hi.2.1 hφ pos]

theorem readPlace_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) (copy : Bool) :
    readPlace K φ p copy s = readPlace K φ' p copy s := by
  unfold readPlace
  rw [← contentOf_congr K hφ hi p]
  cases hc : contentOf K φ p s with
  | none => rfl
  | some x =>
    obtain ⟨⟨v, T, pos, steps⟩, s₁⟩ := x
    have hi₁ := (contentOf_rinv K φ L hc hi).1
    simp only [Bind.bind, Option.bind]
    rw [setContent_congr K hφ hi₁]

theorem borrowPlace_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (p : Place) :
    borrowPlace K φ p s = borrowPlace K φ' p s := by
  unfold borrowPlace
  rw [contentOf_congr K hφ hi p]

theorem movedPlaces_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) :
    movedPlaces φ s = movedPlaces φ' s := by
  unfold movedPlaces
  split
  · congr 1
    funext i
    split
    · rename_i pos _
      rw [closedFuture_read hi.1 hi.2.1 hφ pos]
    · rfl
  · rfl

theorem foldl_inv {α : Type} (P : SState → Prop) (F : SState → α → SState) (h : ∀ s a, P s → P (F s a)) :
    ∀ (qs : List α) (s : SState), P s → P (qs.foldl F s)
  | [], _, hs => hs
  | q :: qs, s, hs => foldl_inv P F h qs _ (h s q hs)

theorem foldl_congr_inv {α : Type} (P : SState → Prop) (F F' : SState → α → SState)
    (h : ∀ s a, P s → F s a = F' s a ∧ P (F s a)) : ∀ (qs : List α) (s : SState), P s → qs.foldl F s = qs.foldl F' s
  | [], _, _ => rfl
  | q :: qs, s, hs => by
    simp only [List.foldl_cons]
    rw [← (h s q hs).1]
    exact foldl_congr_inv P F F' h qs _ (h s q hs).2

/-- The join's drop is the same at both futures. -/
theorem joinDrop_congr (hφ : ∀ l, L l → φ l = φ' l) (entry : List Place) (t : Term) {s : SState} (hi : RInv L s) :
    joinDrop K φ entry t s = joinDrop K φ' entry t s := by
  unfold joinDrop
  apply foldl_congr_inv (RInv L) _ _ _ _ s hi
  intro s q hi
  refine ⟨?_, ?_⟩
  · dsimp only
    split
    · rfl
    · split
      · rename_i pos steps _
        rw [closedFuture_read (access_rinv hi pos).1 (access_rinv hi pos).2.1 hφ pos]
      · rfl
  · dsimp only
    split
    · exact hi
    · split
      · rename_i pos steps hr
        have hia := access_rinv hi pos
        split
        · exact hia
        · exact hia
        · exact hia
        · have hie : RInv L (if steps.isEmpty = true then
              (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
              else s.access pos) := by
            split
            · split
              · exact endLabel_rinv hia _
              · exact hia
            · exact hia
          generalize (if steps.isEmpty = true then
              (match (s.access pos).shape pos with | some l => (s.access pos).endLabel l | none => s.access pos)
              else s.access pos) = s₂ at hie ⊢
          exact setAt_rinv hie pos _
            ((hie.1 pos).comp (fun x => (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps x).getD .err))
            (fun x hx => by
              by_cases hp : pos ∈ s₂.positions
              · exact (hie.2.1 pos x hp hx).comp
                  (fun x => (Sem.updAt K.dm K.Γ (s₂.tyAt pos).m (fun _ => .moved) steps x).getD .err)
              · exact absurd (hie.2.2 pos x hx).1 hp)
      · exact hi

/-- An `Id`'s observation is the same at both futures: after every borrow ends, every position
factors through `L` (R3). -/
theorem observation_congr (hφ : ∀ l, L l → φ l = φ' l) {s : SState} (hi : RInv L s) (reps : List Place)
    (ws : List Sem) (ps₀ : List Pos) (r : Res) : observation φ reps ws ps₀ r s = observation φ' reps ws ps₀ r s := by
  unfold observation
  dsimp only
  have hiS := foldl_inv (RInv L) (fun s (x : Place × Nat) => match resolve s x.1, ws[x.2]? with
      | some (pos, []), some w => s.setAt pos fun _ => w
      | _, _ => s) (fun s x hs => by
        split
        · exact setAt_rinv hs _ _ (FT.const _ _) (fun _ _ => FT.const _ _)
        · exact hs) reps.zipIdx s hi
  congr 1
  apply List.map_congr_left
  intro p _
  exact endAll_FT hiS.1 hiS.2.1 p φ φ' hφ

theorem SM.bind_congr {α β : Type 3} {m m' : SM α} {k k' : α → SM β} {s : SState} (hm : m s = m' s)
    (hk : ∀ a s₁, m s = some (a, s₁) → k a s₁ = k' a s₁) : (m >>= k) s = (m' >>= k') s := by
  simp only [Bind.bind, Monad.toBind, instMonadSM]
  rw [← hm]
  cases h : m s with
  | none => rfl
  | some p => exact hk p.1 p.2 h

theorem Option.bind_congr' {α β : Type _} {x x' : Option α} {f f' : α → Option β} (hx : x = x')
    (hf : ∀ a, x = some a → f a = f' a) : x.bind f = x'.bind f' := by
  rw [← hx]
  cases h : x with
  | none => rfl
  | some a => exact hf a h

/-- A state whose positions hold constants and whose shape is empty has the invariant. -/
theorem rinv_of_const {s : SState} (hc : ∀ p, ∃ c, s.valAt p = fun _ => c) (hsh : ∀ p, s.shape p = none) :
    RInv L s := by
  refine ⟨fun p => ?_, (fun r x _ hs => by rw [hsh] at hs; cases hs), (fun p x hs => by rw [hsh] at hs; cases hs)⟩
  obtain ⟨c, e⟩ := hc p; rw [e]; exact FT.const _ _

theorem rinv_emptyState (n : Nat) : RInv L (emptyState n) :=
  rinv_of_const (fun p => ⟨.err, by
    have : p ∉ (emptyState n).positions := by simp [SState.positions, emptyState]
    rw [valAt_of_not_mem _ _ this]⟩) (fun _ => rfl)

theorem rinv_stateOf (n : Nat) (vs : List Sem) (tys : List (DeclInfo × TyS)) :
    RInv L (stateOf n (capsState vs tys)) := by
  apply rinv_of_const _ (fun _ => rfl)
  intro p
  cases p with
  | temp f i => exact ⟨.err, by simp [SState.valAt, stateOf]; cases f <;> simp⟩
  | bind f i =>
    simp only [SState.valAt, stateOf]
    split
    · rename_i b hb
      cases f with
      | succ f => simp at hb
      | zero =>
        simp only [List.getElem?_cons_zero, Option.bind_some, capsState, List.getElem?_map] at hb
        cases hz : (vs.zip tys)[i]? with
        | none => rw [hz] at hb; cases hb
        | some x => rw [hz] at hb; cases hb; exact ⟨x.1, rfl⟩
    · exact ⟨.err, rfl⟩

theorem rinv_foldl_pushBind : ∀ (bl : List SBinding), (∀ b ∈ bl, ∃ c, b.val = fun _ => c) → ∀ {s : SState},
    RInv L s → RInv L (bl.foldl (fun s b => s.pushBind b) s)
  | [], _, _, hi => hi
  | b :: bl, hb, _, hi => by
    obtain ⟨c, hc⟩ := hb b (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    exact rinv_foldl_pushBind bl (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) (pushBind_rinv hi b c hc)

/-- A frame extended by parameters, at whatever types and readings (`bs`), keeps the invariant:
the bindings hold constants. -/
theorem rinv_extendBy {s : SState} (hi : RInv L s) (bs : List PBind) (acc : List Sem) : RInv L (extendBy s bs acc) := by
  unfold extendBy
  refine rinv_foldl_pushBind _ (fun b hb => ?_) hi
  simp only [extendBinds, List.mem_map] at hb
  obtain ⟨ai, -, rfl⟩ := hb
  exact ⟨ai.1, rfl⟩

end

theorem anyAtomList_of_mem {P : Value → Bool} {t : Term} : ∀ {ts : List Term}, t ∈ ts → t.anyAtom P = true →
    Term.anyAtomList P ts = true
  | a :: as, hm, h => by
    rw [List.mem_cons] at hm
    rcases hm with e | hm
    · subst e; simp [Term.anyAtomList, h]
    · simp [Term.anyAtomList, anyAtomList_of_mem hm h]

/-! ## The fix clause, named

`run`'s `.fix` clause is a block of `let`s; these definitions name its pieces (copied from it,
`run_fix_def` checks they are the same), so the clause's congruence can be stated and proved
outside the mutual induction, with the body's congruence as a hypothesis. -/

section FixDefs
variable (K : RunCtx) (ρ : Assignment) (φ : Future) (fb : List PBind × DeclInfo)

/-- A borrow parameter's or a plain parameter's push into the closure's frame. -/
noncomputable def fixStep (sa : SState × List Sem × List Pos) (ap : Sem × PiParam) : SState × List Sem × List Pos :=
  let (s, acc, cells) := sa
  let T : TyS := match fb.1[acc.length]? with | some b => b.1 acc | none => .plain (ap.2.dom acc)
  let d : DeclInfo := match fb.1[acc.length]? with | some b => b.2 | none => .other
  if ap.2.isRef then
    let (l, s) := s.freshLoan
    let s := s.pushTemp fun ψ => ψ l
    let cell : Pos := .temp s.topIdx (((s.env.getLast?).map (·.temps.length)).getD 1 - 1)
    let s := pushBindShaped s { ty := { T with label := some l }, val := fun _ => ap.1, decl := d }
    (s, acc ++ [ap.1], cells ++ [cell])
  else
    (s.pushBind { ty := { T with label := none }, val := fun _ => ap.1, decl := d }, acc ++ [ap.1], cells)

/-- The closure's body run, at a meaning of `self` and arguments (`bodyAt`). -/
noncomputable def fixBodyAt (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat) (body : Term)
    (selfM : Sem) (args : List Sem) : Option BodyOut :=
  let s₁ := s.pushBind { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM, decl := .pi fb.2 }
  let (s₂, _, cells) := (args.zip ps).foldl (fixStep fb) (s₁, [], [])
  let codT := match out with | .data B => B args | .ref U => U args
  match run K ρ φ (.plain codT) body s₂ with
  | some ((r, R), s₃) =>
    let keep : Option Nat := match out with | .ref _ => R.label | .data _ => none
    let s₄ := (s₃.liveLabels.filter fun l => l ≥ start ∧ some l ≠ keep).foldl SState.endLabel s₃
    let finals := cells.map fun c => s₄.valAt c
    some ⟨r, finals, R.label⟩
  | none => none

/-- The stages of a recursive closure. -/
noncomputable def fixStage (l : Nat) (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat)
    (body : Term) : Nat → List Sem → Option BodyOut :=
  Nat.rec (motive := fun _ => List Sem → Option BodyOut) (fun _ => none)
    (fun _ gk => fixBodyAt K ρ φ fb s ps out piT start body (closureAt l φ ps out gk))

/-- A Π-term's or closure's output type, as a function of the parameters. -/
noncomputable def fixOut (s : SState) (bs : List PBind) (c : Term) : PiOut := match c with
  | .ref U => .ref fun acc => match run K ρ φ (.plain .err) U (extendBy s bs acc) with
    | some ((v, _), _) => v.asTy
    | none => .err
  | c => .data fun acc => match run K ρ φ (.plain .err) c (extendBy s bs acc) with
    | some ((v, _), _) => v.asTy
    | none => .err

/-- The decreasing argument's rank (φ-free). -/
noncomputable def fixRank (ps : List PiParam) (dec : Option Nat) (args : List Sem) : Nat := match dec with
  | some j =>
    match args[j]?, (ps[j]?).map (·.dom (args.take j)) with
    | some a, some T =>
      match T.dataOf K.dm K.Γ with
      | some (d, ps') => match a.as (K.dm.car d ps') with | some x => K.dm.rank x | none => 0
      | none => match a.asNat with | some n => n | none => 0
    | _, _ => 0
  | none => 0

/-- The closure's function: the guarded fixpoint by stages, or the body with `self` erroneous. -/
noncomputable def fixG (l : Nat) (s : SState) (ps : List PiParam) (out : PiOut) (piT : TyM) (start : Nat)
    (dec : Option Nat) (body : Term) : List Sem → Option BodyOut := match dec with
  | some _ => fun args => fixStage K ρ φ fb l s ps out piT start body (fixRank K ps dec args + 1) args
  | none => fixBodyAt K ρ φ fb s ps out piT start body .err

/-- Forming the closure moves its non-copy captures. -/
noncomputable def fixMoves (t : Term) (s : SState) : SState :=
  (Term.freeVars t).foldl (fun s i =>
    if K.D.copy (K.D.placeDecl (scopeOf s) (.var i)) then s
    else match s.varPos i with
      | some pos => s.setAt pos fun _ => .moved
      | none => s) s

theorem run_fix_def (hint : TyS) (self : Hint) (hs : List Hint) (ds : List Term) (c : Term) (dec : Option Nat)
    (body : Term) (s : SState) :
    run K ρ φ hint (.fix self hs ds c dec body) s =
      SM.erasedIf (K.D.flags (scopeOf s) (.fix self hs ds c dec body)) (fun _ => some ((closureAt (K.D.piSort (scopeOf s) (.pi hs ds c)) φ (runDoms K ρ φ s ds) (fixOut K ρ φ s (bindsOf K ρ φ s ds) c)
          (fixG K ρ φ (bindsOf K ρ φ s ds, K.D.typeDecl (K.D.teleDecls (scopeOf s) ds) c) (K.D.piSort (scopeOf s) (.pi hs ds c)) s (runDoms K ρ φ s ds) (fixOut K ρ φ s (bindsOf K ρ φ s ds) c)
            (piTyAt (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ s ds) (fixOut K ρ φ s (bindsOf K ρ φ s ds) c)) s.nextLoan dec body),
        ⟨piTyAt (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ s ds) (fixOut K ρ φ s (bindsOf K ρ φ s ds) c),
          some (runDoms K ρ φ s ds, fixOut K ρ φ s (bindsOf K ρ φ s ds) c), none, none⟩),
        fixMoves K (.fix self hs ds c dec body) s)) s := by
  rw [run]
  rfl

end FixDefs

/-! ## Forming the closure's frame: the cells are ordered at the start -/

section FixProps
variable {L : Nat → Prop} {fb : List PBind × DeclInfo}

/-- A label added to `L` can be dropped again when it is live or read by no one. -/
theorem rinv_drop_one {s : SState} {n : Nat} (h : RInv (fun y => L y ∨ y = n) s)
    (hn : s.Live n ∨ ∀ q, Indep n (s.valAt q)) : RInv L s := by
  obtain ⟨h1, h2, hsa⟩ := h
  rcases hn with hn | hn
  · refine ⟨fun p => (h1 p).mono fun y hy => ?_, fun r x hr hs => (h2 r x hr hs).mono fun y hy => ?_, hsa⟩
    · rcases hy with (hy | rfl) | hy
      · exact .inl hy
      · exact .inr hn
      · exact .inr hy
    · rcases hy with ⟨hy | rfl, hl⟩ | hy
      · exact .inl ⟨hy, hl⟩
      · exact absurd hn hl
      · exact .inr hy
  · refine ⟨fun p => ((h1 p).remove (hn p)).mono fun y ⟨hy, hne⟩ => ?_,
      fun r x hr hs => ((h2 r x hr hs).remove (hn r)).mono fun y ⟨hy, hne⟩ => ?_, hsa⟩
    · rcases hy with (hy | hy) | hy
      · exact .inl hy
      · exact absurd hy hne
      · exact .inr hy
    · rcases hy with ⟨hy | hy, hl⟩ | hy
      · exact .inl ⟨hy, hl⟩
      · exact absurd hy hne
      · exact .inr hy

theorem live_pushTemp {s : SState} (hsa : ShapeAt s) (v : SVal) (y : Nat) : (s.pushTemp v).Live y ↔ s.Live y := by
  rw [live_iff, live_iff]
  constructor
  · rintro ⟨q, _, hs⟩; exact ⟨q, (hsa q y hs).1, hs⟩
  · rintro ⟨q, hq, hs⟩; exact ⟨q, mem_positions_pushTemp s v hq, hs⟩

/-- A cell pushed: it reads `l`, so the invariant holds with `l` added to `L`. -/
theorem rinv_pushTemp_read {s : SState} (hi : RInv L s) (l : Nat) :
    RInv (fun y => L y ∨ y = l) (s.pushTemp fun ψ => ψ l) := by
  obtain ⟨h1, h2, hsa⟩ := hi
  have hlive := live_pushTemp hsa (fun ψ => ψ l)
  refine ⟨fun q => ?_, fun r x _ hs => ?_, fun q x hq => ?_⟩
  · rcases valAt_pushTemp s (fun ψ => ψ l) q with e | e
    · rw [e]; exact (h1 q).mono fun y hy => hy.elim (fun h => .inl (.inl h)) (fun h => .inr ((hlive y).mpr h))
    · rw [e]; intro ψ ψ' hψ; exact hψ l (.inl (.inr rfl))
  · have hs' : s.shape r = some x := hs
    have hr' := (hsa r x hs').1
    rw [valAt_pushTemp_old s _ hr']
    exact (h2 r x hr' hs').mono fun y hy => by
      rcases hy with ⟨hL, hn⟩ | ⟨hy, hxy⟩
      · exact .inl ⟨.inl hL, fun h => hn ((hlive y).mp h)⟩
      · exact .inr ⟨(hlive y).mpr hy, hxy⟩
  · have hq' : s.shape q = some x := hq
    exact ⟨mem_positions_pushTemp s _ (hsa q x hq').1, (hsa q x hq').2⟩

theorem pushTemp_last (s : SState) (v : SVal) (hne : s.env ≠ []) :
    Pos.temp (s.pushTemp v).topIdx ((((s.pushTemp v).env.getLast?).map (·.temps.length)).getD 1 - 1)
      ∈ (s.pushTemp v).positions ∧
    (s.pushTemp v).valAt (Pos.temp (s.pushTemp v).topIdx ((((s.pushTemp v).env.getLast?).map (·.temps.length)).getD 1 - 1)) = v := by
  obtain ⟨fr0, e⟩ : ∃ fr0, s.env.getLast? = some fr0 := by
    cases h : s.env.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
    | some fr0 => exact ⟨fr0, rfl⟩
  have e2 : s.env[s.topIdx]? = some fr0 := by
    rw [List.getLast?_eq_getElem?] at e; simpa [SState.topIdx] using e
  rw [pushTemp_getLast, e, pushTemp_topIdx]
  simp only [Option.map_some, Option.getD_some, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  constructor
  · rw [mem_positions]
    simp only [lookup, SState.pushTemp, List.getElem?_modify, e2]
    simp
  · simp [SState.valAt, SState.pushTemp, List.getElem?_modify, e2]

/-- The forming invariant: the frame's state has the invariant, the counter is past the start, and
every cell is a temporary ordered at the start (or the state has no frame at all). -/
def FormInv (L : Nat → Prop) (start : Nat) (sa : SState × List Sem × List Pos) : Prop :=
  RInv L sa.1 ∧ start ≤ sa.1.nextLoan ∧
    ∀ c ∈ sa.2.2, IsTemp c ∧ ((c ∈ sa.1.positions ∧ Ordered L sa.1 start (sa.1.valAt c)) ∨ sa.1.env = [])

theorem valAt_pushBind_old (s : SState) (b : SBinding) {q : Pos} (hq : q ∈ s.positions) :
    (s.pushBind b).valAt q = s.valAt q := by
  rw [valAt_eq, valAt_eq, lookup_pushBind_old s b q ((mem_positions s q).mp hq)]

theorem nextLoan_pushBindShaped (s : SState) (b : SBinding) : (pushBindShaped s b).nextLoan = s.nextLoan := by
  unfold pushBindShaped
  split
  · dsimp only; split <;> exact (shapeSub_takeLabel s _).2
  · rfl

theorem env_nil_of_envLe {s s' : SState} (h : EnvLe s s') (he : s.env = []) : s'.env = [] :=
  List.eq_nil_of_length_eq_zero (by rw [h.1, he]; rfl)

theorem indep_of_env_nil {s : SState} (he : s.env = []) (y : Nat) (q : Pos) : Indep y (s.valAt q) := by
  have : q ∉ s.positions := by rw [positions_eq, he]; simp
  rw [valAt_of_not_mem _ _ this]; intro _ _; rfl

theorem fixStep_inv {start : Nat} {sa : SState × List Sem × List Pos} (h : FormInv L start sa) (ap : Sem × PiParam) :
    FormInv L start (fixStep fb sa ap) := by
  obtain ⟨s, acc, cells⟩ := sa
  obtain ⟨hi, hst, hcells⟩ := h
  dsimp only at hi hst hcells
  unfold fixStep
  dsimp only
  split
  · simp only [SState.freshLoan]
    generalize hs₀ : ({ s with nextLoan := s.nextLoan + 1 } : SState) = s₀
    have hi₀ : RInv L s₀ := by rw [← hs₀]; exact freshLoan_rinv hi
    have hpos₀ : s₀.positions = s.positions := by rw [← hs₀]; rfl
    have hval₀ : ∀ q, s₀.valAt q = s.valAt q := by intro q; rw [← hs₀]; rfl
    have hlive₀ : ∀ y, s₀.Live y ↔ s.Live y := by intro y; rw [← hs₀]; rfl
    have hshape₀ : s₀.shape = s.shape := by rw [← hs₀]
    have hnl₀ : s₀.nextLoan = s.nextLoan + 1 := by rw [← hs₀]
    have henv₀ : s₀.env = s.env := by rw [← hs₀]
    generalize hT : (s₀.pushTemp fun ψ => ψ s.nextLoan) = T
    have hiT : RInv (fun y => L y ∨ y = s.nextLoan) T := by rw [← hT]; exact rinv_pushTemp_read hi₀ _
    have hliveT : ∀ y, T.Live y ↔ s.Live y := by
      intro y; rw [← hT, live_pushTemp hi₀.2.2, hlive₀]
    have hshapeT : T.shape = s.shape := by rw [← hT, ← hshape₀]; rfl
    have hnlT : T.nextLoan = s.nextLoan + 1 := by rw [← hT, ← hnl₀]; rfl
    generalize hb : ({ ty := { (match fb.1[acc.length]? with | some b => b.1 acc | none => TyS.plain (ap.2.dom acc)) with label := some s.nextLoan }, val := fun _ => ap.1, decl := (match fb.1[acc.length]? with | some b => b.2 | none => DeclInfo.other) } : SBinding) = b
    have hbl : b.ty.label = some s.nextLoan := by rw [← hb]
    have hi'' : RInv (fun y => L y ∨ y = s.nextLoan) (pushBindShaped T b) :=
      pushBindShaped_rinv hiT b ap.1 (by rw [← hb]) fun l hl => by
        rw [hbl] at hl; cases hl
        refine ⟨.inr (.inl fun q x hq => ?_), by rw [hnlT]; exact Nat.lt_succ_self _⟩
        rw [hshapeT] at hq; exact (hi.2.2 q x hq).2
    have henvT : T.env.length = s.env.length := by rw [← hT, (envLe_pushTemp _ _).1, henv₀]
    have henv' : (pushBindShaped T b).env.length = s.env.length := by
      rw [(envPush_pushBindShaped T b).1, henvT]
    by_cases he : s.env = []
    · have he' : (pushBindShaped T b).env = [] := List.eq_nil_of_length_eq_zero (by rw [henv', he]; rfl)
      refine ⟨rinv_drop_one hi'' (.inr (indep_of_env_nil he' _)), ?_, fun c hc => ?_⟩
      · rw [nextLoan_pushBindShaped, hnlT]; exact Nat.le_succ_of_le hst
      · rcases List.mem_append.mp hc with hc | hc
        · exact ⟨(hcells c hc).1, .inr he'⟩
        · simp only [List.mem_singleton] at hc; subst hc; exact ⟨trivial, .inr he'⟩
    · have hneT : T.env ≠ [] := fun h => he (List.eq_nil_of_length_eq_zero (by rw [← henvT, h]; rfl))
      have hlive' : ∀ y, (pushBindShaped T b).Live y ↔ s.Live y ∨ y = s.nextLoan := by
        intro y
        rw [live_pushBindShaped hiT.2.2 b hneT y, hliveT, hbl]
        constructor
        · rintro (h | h)
          · exact .inl h
          · exact .inr (Option.some.inj h).symm
        · rintro (h | h)
          · exact .inl h
          · exact .inr (by rw [h])
      refine ⟨rinv_drop_one hi'' (.inl ((hlive' _).mpr (.inr rfl))), ?_, fun c hc => ?_⟩
      · rw [nextLoan_pushBindShaped, hnlT]; exact Nat.le_succ_of_le hst
      · have hmemT : ∀ q ∈ s.positions, q ∈ T.positions := fun q hq => by
          rw [← hT]; exact mem_positions_pushTemp _ _ (by rw [hpos₀]; exact hq)
        have hvalT : ∀ q ∈ s.positions, T.valAt q = s.valAt q := fun q hq => by
          rw [← hT, valAt_pushTemp_old _ _ (by rw [hpos₀]; exact hq), hval₀]
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨ht, hc'⟩ := hcells c hc
          rcases hc' with ⟨hcm, ho⟩ | he''
          · refine ⟨ht, .inl ⟨mem_positions_pushBindShaped b (hmemT c hcm), ?_⟩⟩
            refine ordered_step ho ?_ (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
            · rcases valAt_pushBindShaped_old b (hmemT c hcm) with e | e
              · exact .inl (by rw [e, hvalT c hcm])
              · exact .inr ⟨_, e⟩
            · rcases (hlive' y).mp h1 with h | rfl
              · exact absurd h h2
              · exact .inl hst
            · exact absurd ((hlive' y).mpr (.inl h1)) h2
          · exact absurd he'' he
        · simp only [List.mem_singleton] at hc
          subst hc
          rw [← hT] at hneT ⊢
          have hne₀ : s₀.env ≠ [] := by rw [henv₀]; exact he
          obtain ⟨hm, hv⟩ := pushTemp_last s₀ (fun ψ => ψ s.nextLoan) hne₀
          refine ⟨trivial, .inl ⟨mem_positions_pushBindShaped b hm, ?_⟩⟩
          rw [hT] at hm hv ⊢
          rcases valAt_pushBindShaped_old b hm with e | e
          · rw [e, hv]
            intro ψ ψ' hψ
            exact hψ s.nextLoan (.inr ⟨(hlive' _).mpr (.inr rfl), hst⟩)
          · rw [e]; exact FT.const _ _
  · refine ⟨pushBind_rinv hi _ ap.1 rfl, hst, fun c hc => ?_⟩
    obtain ⟨ht, hc'⟩ := hcells c hc
    refine ⟨ht, ?_⟩
    rcases hc' with ⟨hcm, ho⟩ | he
    · refine .inl ⟨mem_positions_pushBind _ _ hcm, ?_⟩
      rw [valAt_pushBind_old _ _ hcm]
      exact ordered_step ho (.inl rfl)
        (fun y h1 h2 => absurd ((live_pushBind hi.2.2 _ y).mp h1) h2)
        (fun y h1 h2 => absurd ((live_pushBind hi.2.2 _ y).mpr h1) h2)
    · exact .inr (by simp [SState.pushBind, he])

theorem foldl_fixStep_inv {start : Nat} : ∀ (xs : List (Sem × PiParam)) (sa : SState × List Sem × List Pos),
    FormInv L start sa → FormInv L start (xs.foldl (fixStep fb) sa)
  | [], _, h => h
  | x :: xs, sa, h => foldl_fixStep_inv xs _ (fixStep_inv h x)

end FixProps

/-! ## The closure's body at two futures, and its finals -/

section FixCongr
variable (K : RunCtx) (ρ : Assignment) {φ φ' : Future} {L : Nat → Prop} {fb : List PBind × DeclInfo}

theorem formInv_init {s : SState} (hi : RInv L s) (b : SBinding) (c : Sem) (hb : b.val = fun _ => c) :
    FormInv L s.nextLoan (s.pushBind b, [], []) :=
  ⟨pushBind_rinv hi b c hb, Nat.le_refl _, fun _ hc => by cases hc⟩

theorem fixBodyAt_congr {body : Term} (hb : ∀ hint s₂, RInv L s₂ → run K ρ φ hint body s₂ = run K ρ φ' hint body s₂)
    {s : SState} (hi : RInv L s) (ps : List PiParam) (out : PiOut) (piT : TyM) (selfM : Sem) (args : List Sem) :
    fixBodyAt K ρ φ fb s ps out piT s.nextLoan body selfM args = fixBodyAt K ρ φ' fb s ps out piT s.nextLoan body selfM args := by
  unfold fixBodyAt
  dsimp only
  have hF := foldl_fixStep_inv (fb := fb) (args.zip ps) _
    (formInv_init (L := L) hi { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM, decl := .pi fb.2 } selfM rfl)
  generalize (args.zip ps).foldl (fixStep fb) (s.pushBind { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM, decl := .pi fb.2 }, [], []) = F at hF ⊢
  obtain ⟨s₂, acc, cells⟩ := F
  dsimp only
  rw [hb _ s₂ hF.1]

/-- After the pop, a cell reads `L` and the kept label (`ordered_after_pop`; a state with no frame
has no positions). -/
theorem finals_of_pop {s₂ s₃ : SState} {start : Nat} (hi₃ : RInv L s₃) (e₃ : EnvLe s₂ s₃) (o₃ : OrdKeep L s₂ s₃)
    (hst₂ : start ≤ s₂.nextLoan) {cells : List Pos}
    (hcells : ∀ c ∈ cells, IsTemp c ∧ ((c ∈ s₂.positions ∧ Ordered L s₂ start (s₂.valAt c)) ∨ s₂.env = []))
    (keep : Option Nat) : ∀ c ∈ cells, FT (fun y => L y ∨ some y = keep)
      (((s₃.liveLabels.filter fun l => decide (l ≥ start ∧ some l ≠ keep)).foldl endLabel s₃).valAt c) := by
  intro c hc
  obtain ⟨ht, hc'⟩ := hcells c hc
  rcases hc' with ⟨hcm, ho⟩ | he
  · exact ordered_after_pop hi₃.1 hi₃.2.1 _ _ (o₃.2 _ c hst₂ ht hcm ho)
  · have he₄ := env_nil_of_envLe (envLe_foldl_endLabel
      (s₃.liveLabels.filter fun l => decide (l ≥ start ∧ some l ≠ keep)) s₃) (env_nil_of_envLe e₃ he)
    have : c ∉ ((s₃.liveLabels.filter fun l => decide (l ≥ start ∧ some l ≠ keep)).foldl endLabel s₃).positions := by
      rw [positions_eq, he₄]; simp
    rw [valAt_of_not_mem _ _ this]; exact FT.const _ _

theorem fixBodyAt_finals (hK : ∀ n, (K.C.global n).2.label = none) {s : SState} (hi : RInv L s)
    (ps : List PiParam) (out : PiOut) (piT : TyM) (body : Term) (selfM : Sem) (args : List Sem) (o : BodyOut)
    (h : fixBodyAt K ρ φ fb s ps out piT s.nextLoan body selfM args = some o) : FinalsIn L out o := by
  have hF := foldl_fixStep_inv (fb := fb) (args.zip ps) _
    (formInv_init (L := L) hi { ty := ⟨piT, some (ps, out), none, none⟩, val := fun _ => selfM, decl := .pi fb.2 } selfM rfl)
  cases out with
  | data B =>
    unfold fixBodyAt at h
    dsimp only at h
    generalize hFF : (args.zip ps).foldl (fixStep fb) (s.pushBind { ty := ⟨piT, some (ps, PiOut.data B), none, none⟩, val := fun _ => selfM, decl := .pi fb.2 }, [], []) = F at hF h
    obtain ⟨s₂, acc, cells⟩ := F
    obtain ⟨hi₂, hst₂, hcells⟩ := hF
    dsimp only at h hi₂ hst₂ hcells
    split at h
    · rename_i r R s₃ hrun
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hi₃, -, e₃, o₃⟩ := run_rinv K ρ φ L hK body _ s₂ s₃ (r, R) hi₂ hrun
      have hcell := finals_of_pop hi₃ e₃ o₃ hst₂ hcells none
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact (hcell c₀ hc₀).mono fun y hy => hy.resolve_right (by simp)
    · cases h
  | ref U =>
    unfold fixBodyAt at h
    dsimp only at h
    generalize hFF : (args.zip ps).foldl (fixStep fb) (s.pushBind { ty := ⟨piT, some (ps, PiOut.ref U), none, none⟩, val := fun _ => selfM, decl := .pi fb.2 }, [], []) = F at hF h
    obtain ⟨s₂, acc, cells⟩ := F
    obtain ⟨hi₂, hst₂, hcells⟩ := hF
    dsimp only at h hi₂ hst₂ hcells
    split at h
    · rename_i r R s₃ hrun
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hi₃, -, e₃, o₃⟩ := run_rinv K ρ φ L hK body _ s₂ s₃ (r, R) hi₂ hrun
      have hcell := finals_of_pop hi₃ e₃ o₃ hst₂ hcells R.label
      intro c hc k hk
      simp only [List.mem_map] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      exact (hcell c₀ hc₀).mono fun y hy => hy.imp_right fun e => by
        simp only at hk; rw [hk] at e; exact Option.some.inj e
    · cases h

/-- **The stages of a recursive closure** agree at the two futures, and every stage's finals read
only `L` and the returned label: by induction on the stage, with `closureAt_congr` for `self`. -/
theorem fixStage_congr {body : Term} (hK : ∀ n, (K.C.global n).2.label = none) (hφ : ∀ l, L l → φ l = φ' l)
    (hb : ∀ hint s₂, RInv L s₂ → run K ρ φ hint body s₂ = run K ρ φ' hint body s₂)
    {s : SState} (hi : RInv L s) (l : Nat) (ps : List PiParam) (out : PiOut) (piT : TyM) :
    ∀ k, fixStage K ρ φ fb l s ps out piT s.nextLoan body k = fixStage K ρ φ' fb l s ps out piT s.nextLoan body k ∧
      ∀ args o, fixStage K ρ φ fb l s ps out piT s.nextLoan body k args = some o → FinalsIn L out o
  | 0 => ⟨rfl, fun _ _ h => by cases h⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := fixStage_congr hK hφ hb hi l ps out piT k
    have hcl : closureAt l φ ps out (fixStage K ρ φ fb l s ps out piT s.nextLoan body k)
        = closureAt l φ' ps out (fixStage K ρ φ' fb l s ps out piT s.nextLoan body k) := by
      rw [← ih1]; exact closureAt_congr hφ l ps out _ ih2
    refine ⟨?_, fun args o h => ?_⟩
    · show fixBodyAt K ρ φ fb s ps out piT s.nextLoan body (closureAt l φ ps out (fixStage K ρ φ fb l s ps out piT s.nextLoan body k))
        = fixBodyAt K ρ φ' fb s ps out piT s.nextLoan body (closureAt l φ' ps out (fixStage K ρ φ' fb l s ps out piT s.nextLoan body k))
      rw [hcl]
      funext args
      exact fixBodyAt_congr K ρ hb hi ps out piT _ args
    · exact fixBodyAt_finals K ρ hK hi ps out piT body _ args o h

theorem fixG_congr {body : Term} (hK : ∀ n, (K.C.global n).2.label = none) (hφ : ∀ l, L l → φ l = φ' l)
    (hb : ∀ hint s₂, RInv L s₂ → run K ρ φ hint body s₂ = run K ρ φ' hint body s₂)
    {s : SState} (hi : RInv L s) (l : Nat) (ps : List PiParam) (out : PiOut) (piT : TyM) (dec : Option Nat) :
    fixG K ρ φ fb l s ps out piT s.nextLoan dec body = fixG K ρ φ' fb l s ps out piT s.nextLoan dec body ∧
      ∀ args o, fixG K ρ φ fb l s ps out piT s.nextLoan dec body args = some o → FinalsIn L out o := by
  cases dec with
  | none =>
    refine ⟨funext fun args => fixBodyAt_congr K ρ hb hi ps out piT _ args, fun args o h => ?_⟩
    exact fixBodyAt_finals K ρ hK hi ps out piT body _ args o h
  | some j =>
    refine ⟨funext fun args => ?_, fun args o h => ?_⟩
    · exact congrFun (fixStage_congr K ρ hK hφ hb hi l ps out piT (fixRank K ps (some j) args + 1)).1 args
    · exact (fixStage_congr K ρ hK hφ hb hi l ps out piT (fixRank K ps (some j) args + 1)).2 args o h

end FixCongr

/-- The type an embedded value's run carries (`run`'s `.val` clause). -/
noncomputable def valT (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) : Value → TyS
  | .clo caps t rd => { hint with shape := ((piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps)
      (capsTys K ρ φ rd))) t).map fun sh => (sh.ps, sh.out)) }
  | .tPi caps t rd => { hint with shape := ((piShapeOf K ρ φ (stateOf 0 (capsState (capsVals K ρ φ caps)
      (capsTys K ρ φ rd))) t).map fun sh => (sh.ps, sh.out)) }
  | .gfn n => (K.C.global n).2
  | .abs σ => { hint with shape := (K.Δ σ).shape, data := (K.Δ σ).data }
  | .loan l => match (K.Λ l).shape with
    | some sh => { hint with shape := some sh }
    | none => hint
  | .sealed t => match run K ρ φ hint t (emptyState 0) with
    | some ((_, R), _) => { hint with shape := R.shape }
    | none => hint
  | _ => hint

theorem run_val_def (K : RunCtx) (ρ : Assignment) (φ : Future) (hint : TyS) (v : Value) (s : SState) :
    run K ρ φ hint (.val v) s = some ((meanV K ρ φ hint v, { valT K ρ φ hint v with label := none }), s) := by
  cases v <;> rfl

theorem SM.onCopy_congr {α : Type 3} {x x' : SM α} {s : SState} (h : x s = x' s) :
    SM.onCopy x s = SM.onCopy x' s := by
  unfold SM.onCopy; rw [h]

section
variable (K : RunCtx) (ρ : Assignment) (φ φ' : Future)

mutual
/-- **Part (E)**: the run at two futures that agree on `L`, from a state with `RInv L`, of a term
whose loans are in `L`, is the same. -/
theorem run_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (t : Term) (hint : TyS) (s : SState)
    (L : Nat → Prop), (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s →
    run K ρ φ hint t s = run K ρ φ' hint t s
  | .place p, hint, s, L, hφ, ht, hi => by
    rw [run, run]; exact SM.erasedIf_congr (readPlace_congr K hφ hi p _)
  | .borrow p, hint, s, L, hφ, ht, hi => by
    rw [run, run]; exact SM.erasedIf_congr (borrowPlace_congr K hφ hi p)
  | .seq u w, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ h1
    exact run_congrE hK w hint s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h]))
      (run_rinv K ρ φ L hK u _ s s₁ a hi h1).1
  | .succ u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ _; rfl
  | .ref A, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro a s₁ _; rfl
  | .const n, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .sort l, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .nat, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .unit, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .zero, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .tt, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .cong f g, hint, s, L, hφ, ht, hi => by rw [run, run]
  | .val v, hint, s, L, hφ, ht, hi => by
    have hv : ∀ l, v.hasLoan l = true → φ l = φ' l := fun l h => hφ l (ht l h)
    rw [run_val_def, run_val_def, meanV_congrE hK v hint hv]
    cases v with
    | clo caps t rd =>
      simp only [valT]
      rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        piShapeOf_congrE hK t _ (fun l => φ l = φ' l) (fun _ h => h)
          (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
    | tPi caps t rd =>
      simp only [valT]
      rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
        piShapeOf_congrE hK t _ (fun l => φ l = φ' l) (fun _ h => h)
          (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
    | sealed t =>
      simp only [valT]
      rw [run_congrE hK t hint _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_emptyState _)]
    | _ => rfl
  | .ascribe u A, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi))
    rintro ⟨TA, _⟩ s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (run_congrE hK u _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    intro _ _ _; rfl
  | .eq A a b, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply SM.onCopy_congr
    apply SM.bind_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨TA, _⟩ s₁ h1
    have hi₁ := (run_rinv K ρ φ L hK A _ s s₁ _ hi h1).1
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK a _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁))
    rintro ⟨va, _⟩ s₂ h2
    have e := SM.onCopy_state h2
    subst e
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK b _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁))
    intro _ _ _; rfl
  | .id A t u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    apply Option.bind_congr' (SM.onCopy_congr (run_congrE hK A _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi))
    rintro ⟨⟨TA, _⟩, s₁⟩ _
    apply Option.bind_congr' (run_congrE hK t _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨r₁, s₁'⟩ h2
    apply Option.bind_congr' (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨r₂, s₂'⟩ h3
    have hi₁ := (run_rinv K ρ φ L hK t _ s s₁' r₁ hi h2).1
    have hi₂ := (run_rinv K ρ φ L hK u _ s s₂' r₂ hi h3).1
    simp only [observation_congr hφ hi₁, observation_congr hφ hi₂]
  | .tind n args, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    cases hd : K.Γ.find? (·.name == n) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrE hK d args 0 [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro _ _ _; rfl
  | .call f args hd, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    dsimp only
    refine SM.erasedIf_congr ?_
    -- the head: a place in place, anything else by its run
    have hhead : SM.headOf f (fun p => readPlace K φ p true) (run K ρ φ (.plain .err) f) s
        = SM.headOf f (fun p => readPlace K φ' p true) (run K ρ φ' (.plain .err) f) s :=
      SM.headOf_congr (fun p => readPlace_congr K hφ hi p true)
        (run_congrE hK f _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    apply SM.bind_congr hhead
    intro fv s₁ h1
    have hi₁ : RInv L s₁ := by
      rcases SM.headOf_some h1 with ⟨p, h1⟩ | h1
      · exact (readPlace_rinv K φ L h1 hi).1
      · exact (run_rinv K ρ φ L hK f _ s s₁ fv hi h1).1
    apply SM.bind_congr (runArgs_congrE hK _ _ args 0 [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
    intro _ _ _; rfl
  | .matchNat p z u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    dsimp only
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' rfl
    rintro ⟨⟨v, T, pos, steps⟩, s₁⟩ h1
    have hi₁ := (contentOf_rinv K φ' L h1 hi).1
    dsimp only
    rw [movedPlaces_congr hφ hi₁]
    split
    · apply Option.bind_congr' (run_congrE hK z hint s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      rw [joinDrop_congr K hφ _ _ (run_rinv K ρ φ L hK z hint s₁ s₂ _ hi₁ h2).1]
    · apply Option.bind_congr' (run_congrE hK u hint s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      rw [joinDrop_congr K hφ _ _ (run_rinv K ρ φ L hK u hint s₁ s₂ _ hi₁ h2).1]
    · rfl
  | .matchInd p n arms, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    dsimp only
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' rfl
    rintro ⟨⟨v, T, pos, steps⟩, s₁⟩ h1
    have hi₁ := (contentOf_rinv K φ' L h1 hi).1
    dsimp only
    rw [movedPlaces_congr hφ hi₁]
    split
    · rename_i c _
      apply Option.bind_congr' (runArm_congrE hK arms hint c s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₁)
      rintro ⟨⟨r, R⟩, s₂⟩ h2
      rw [joinDrop_congr K hφ _ _ (runArm_rinv K ρ φ L hK arms hint c s₁ s₂ _ hi₁ h2).1]
    · rfl
  | .letIn x u w, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    apply Option.bind_congr' (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨⟨v, T⟩, s₁⟩ h1
    obtain ⟨hi₁, hy₁, -, -⟩ := run_rinv K ρ φ L hK u _ s s₁ (v, T) hi h1
    have hi₂ := pushBindShaped_rinv hi₁ { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s₁) u } v rfl
      fun l hl => by
        rcases hy₁ l hl with ⟨h' | h', hn⟩
        · exact ⟨.inl h', hn⟩
        · exact ⟨.inr (.inr h'), hn⟩
    dsimp only
    apply Option.bind_congr' (run_congrE hK w hint _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₂)
    intro _ _; rfl
  | .assign p u, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    -- the place's type (read on a discarded copy), then the right-hand side, then the access
    rw [contentOf_congr K hφ hi p]
    apply Option.bind_congr' (run_congrE hK u _ s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
    rintro ⟨⟨v, R⟩, s₁⟩ h2
    have hi₁ := (run_rinv K ρ φ L hK u _ s s₁ _ hi h2).1
    dsimp only
    cases hr : resolve s₁ p with
    | none => rfl
    | some ps =>
    obtain ⟨pos, steps⟩ := ps
    dsimp only
    have hi₂ : RInv L (if (steps.isEmpty && (s₁.shape pos).isSome) = true then s₁ else s₁.access pos) := by
      split
      · exact hi₁
      · exact access_rinv hi₁ pos
    generalize (if (steps.isEmpty && (s₁.shape pos).isSome) = true then s₁ else s₁.access pos) = s₂ at hi₂ ⊢
    rw [setContent_congr K hφ ?_ pos steps v]
    split
    · split
      · exact endLabel_rinv hi₂ _
      · exact hi₂
    · exact hi₂
  | .pi hs ds c, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    have hbs := runBinds_congrE hK s L hφ hi (K.D.paramDecls (scopeOf s) ds) ds []
      (fun l h => ht l (by simp [Term.anyAtom, h]))
    have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run K ρ φ' (.plain .err) c (extendBy s bs acc) :=
      fun bs acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
    dsimp only
    rw [hbs]
    cases c with
    | ref U =>
      have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run K ρ φ' (.plain .err) U (extendBy s bs acc) :=
        fun bs acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
      simp only [hU]
    | _ => simp only [hc]
  | .ctor ty c hh ps args, hint, s, L, hφ, ht, hi => by
    rw [run, run]
    refine SM.erasedIf_congr ?_
    cases hd : K.Γ.find? (·.name == ty) with
    | none => rfl
    | some d =>
      apply SM.bind_congr (runParams_congrE hK d ps 0 [] s L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi)
      intro psM s₁ h1
      have e := runParams_state K ρ φ d ps 0 [] s s₁ psM h1
      subst e
      have cont : ∀ ps' : List Sem, (if d.sort == 0 then
            (do let _ ← runFields K ρ φ true d ps' c 0 [] args
                pure ((.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))
          else
            (do let fs ← runFields K ρ φ false d ps' c 0 [] args
                pure ((K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))) s₁
          = (if d.sort == 0 then
            (do let _ ← runFields K ρ φ' true d ps' c 0 [] args
                pure ((.proof, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))
          else
            (do let fs ← runFields K ρ φ' false d ps' c 0 [] args
                pure ((K.dm.ctorM d ps' c fs, ⟨K.dm.tyM d ps', none, none, some (ty, ps')⟩) : Res))) s₁ := by
        intro ps'
        have hF := fun b => runFields_congrE hK b d ps' c args 0 [] s₁ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi
        by_cases hs0 : (d.sort == 0) = true
        · rw [if_pos hs0, if_pos hs0]
          exact SM.bind_congr (hF true) (fun _ _ _ => rfl)
        · rw [if_neg hs0, if_neg hs0]
          exact SM.bind_congr (hF false) (fun _ _ _ => rfl)
      by_cases hc : (ps.isEmpty && !d.params.isEmpty) = true
      · rw [if_pos hc]
        cases hdata : hint.data with
        | none => rfl
        | some np =>
          obtain ⟨n', ps''⟩ := np
          dsimp only
          by_cases hn : n' = ty
          · rw [if_pos hn]; exact cont ps''
          · rw [if_neg hn]
      · rw [if_neg hc]
        exact cont psM
  | .prim n args, hint, s, L, hφ, ht, hi => by
    have hall : ∀ t ∈ args, ∀ (hint : TyS) (s : SState), RInv L s →
        run K ρ φ hint t s = run K ρ φ' hint t s := fun t hm hint s hi =>
      runAll_congrE hK args t hm hint s L hφ
        (fun l h => ht l (by simp only [Term.anyAtom]; exact anyAtomList_of_mem hm h)) hi
    by_cases h1 : n = "symm"
    · subst h1; rw [run, run]
    by_cases h2 : n = "trans"
    · subst h2; rw [run, run]
    by_cases h3 : n = "rewrite"
    · subst h3; rw [run, run]
    by_cases h4 : n = "rewriteR"
    · subst h4; rw [run, run]
    by_cases hJ : ∃ A a b P h t, n = "J" ∧ args = [A, a, b, P, h, t]
    · obtain ⟨A, a, b, P, h', t, rfl, hargs⟩ := hJ
      have hm : ∀ x, x ∈ [A, a, b, P, h', t] → x ∈ args := fun x hx => by rw [hargs]; exact hx
      rw [hargs, run, run]
      refine SM.erasedIf_congr ?_
      apply SM.bind_congr (SM.onCopy_congr (hall A (hm A (by simp)) _ s hi))
      intro _ s₁ e1; have e := SM.onCopy_state e1; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall a (hm a (by simp)) _ _ hi))
      intro _ s₂ e2; have e := SM.onCopy_state e2; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall b (hm b (by simp)) _ _ hi))
      intro _ s₃ e3; have e := SM.onCopy_state e3; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall P (hm P (by simp)) _ _ hi))
      intro _ s₄ e4; have e := SM.onCopy_state e4; subst e
      apply SM.bind_congr (SM.onCopy_congr (hall h' (hm h' (by simp)) _ _ hi))
      intro _ s₅ e5; have e := SM.onCopy_state e5; subst e
      exact hall t (hm t (by simp)) _ _ hi
    by_cases hc : ∃ u, (n = "clone" ∨ n = "peek" ∨ n = "inplace") ∧ args = [u]
    · obtain ⟨u, hn, hargs⟩ := hc
      have hu : u ∈ args := by rw [hargs]; simp
      rcases hn with rfl | rfl | rfl <;>
        (rw [hargs, run, run]
         exact SM.erasedIf_congr (SM.headOf_congr (fun p => readPlace_congr K hφ hi p true) (hall u hu _ _ hi)))
    have hJ' : ∀ (A a b P h t : Term), n = "J" → args = [A, a, b, P, h, t] → False :=
      fun A a b P h t e1 e2 => hJ ⟨A, a, b, P, h, t, e1, e2⟩
    have hc1 : ∀ u, n = "clone" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inl e1, e2⟩
    have hc2 : ∀ u, n = "peek" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inl e1), e2⟩
    have hc3 : ∀ u, n = "inplace" → args = [u] → False := fun u e1 e2 => hc ⟨u, .inr (.inr e1), e2⟩
    rw [run.eq_39 K ρ φ hint n args h1 h2 h3 h4 hJ' hc1 hc2 hc3,
      run.eq_39 K ρ φ' hint n args h1 h2 h3 h4 hJ' hc1 hc2 hc3]
  | .fix self hs ds c dec body, hint, s, L, hφ, ht, hi => by
    have hbs : bindsOf K ρ φ s ds = bindsOf K ρ φ' s ds :=
      runBinds_congrE hK s L hφ hi (K.D.paramDecls (scopeOf s) ds) ds [] (fun l h => ht l (by simp [Term.anyAtom, h]))
    have hds : runDoms K ρ φ s ds = runDoms K ρ φ' s ds := by unfold runDoms; rw [hbs]
    have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run K ρ φ' (.plain .err) c (extendBy s bs acc) :=
      fun bs acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
    have hb : ∀ (hint : TyS) (s₂ : SState), RInv L s₂ → run K ρ φ hint body s₂ = run K ρ φ' hint body s₂ :=
      fun hint s₂ hi₂ => run_congrE hK body hint s₂ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) hi₂
    have hout : ∀ bs, fixOut K ρ φ s bs c = fixOut K ρ φ' s bs c := by
      intro bs
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run K ρ φ' (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
        simp only [fixOut, hU]
      | _ => simp only [fixOut, hc]
    rw [run_fix_def, run_fix_def, hds, hbs, hout]
    obtain ⟨hg1, hg2⟩ := fixG_congr K ρ hK hφ hb hi (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ' s ds)
      (fixOut K ρ φ' s (bindsOf K ρ φ' s ds) c)
      (piTyAt (K.D.piSort (scopeOf s) (.pi hs ds c)) (runDoms K ρ φ' s ds) (fixOut K ρ φ' s (bindsOf K ρ φ' s ds) c)) dec
    rw [← hg1, closureAt_congr hφ _ _ _ _ hg2]

theorem meanV_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (v : Value) (hint : TyS),
    (∀ l, v.hasLoan l = true → φ l = φ' l) → meanV K ρ φ hint v = meanV K ρ φ' hint v
  | .loan l, hint, hv => hv l (by
      show (Value.loan l).anyAtom (· == .loan l) = true
      unfold Value.anyAtom
      show (Value.beq (.loan l) (.loan l) || _) = true
      simp [Value.beq])
  | .succ w, hint, hv => by
    show (meanV K ρ φ _ w).succ = (meanV K ρ φ' _ w).succ
    rw [meanV_congrE hK w _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom] at h ⊢; simp [h])]
  | .borrow _ w, hint, hv => by
    show meanV K ρ φ hint w = meanV K ρ φ' hint w
    exact meanV_congrE hK w hint fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h])
  | .tRef A, hint, hv => by
    show meanV K ρ φ _ A = meanV K ρ φ' _ A
    exact meanV_congrE hK A _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h])
  | .tEq A a b, hint, hv => by
    rw [meanV, meanV]
    rw [meanV_congrE hK A _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h]),
      meanV_congrE hK a _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h]),
      meanV_congrE hK b _ fun l h => hv l (by simp [Value.hasLoan] at h ⊢; simp [Value.anyAtom, h])]
  | .clo caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      run_congrE hK t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
  | .tPi caps t rd, hint, hv => by
    rw [meanV, meanV]
    rw [capsVals_congrE hK caps fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      capsTys_congrE hK rd fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h]),
      run_congrE hK t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_stateOf _ _ _)]
  | .sealed t, hint, hv => by
    rw [meanV, meanV]
    rw [run_congrE hK t _ _ (fun l => φ l = φ' l) (fun _ h => h)
        (fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])) (rinv_emptyState _)]
  | .ind ty c h ps fs, hint, hv => by
    rw [meanV, meanV]
    split
    · rename_i d _
      dsimp only
      rw [meanParams_congrE hK d ps _ _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])]
      split
      · rename_i ps' _
        rw [meanFields_congrE hK d ps' c fs _ _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])]
      · rfl
    · rfl
  | .tInd n args, hint, hv => by
    rw [meanV, meanV]
    split
    · rename_i d _
      rw [meanParams_congrE hK d args _ _ fun l h => hv l (by simp [Value.hasLoan, Value.anyAtom, h])]
    · rfl
  | .zero, _, _ => rfl
  | .unit, _, _ => rfl
  | .gfn _, _, _ => rfl
  | .bot, _, _ => rfl
  | .abs _, _, _ => rfl
  | .proof, _, _ => rfl
  | .tNat, _, _ => rfl
  | .tUnit, _, _ => rfl
  | .sort _, _, _ => rfl

theorem runAll_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (ts : List Term) (t : Term), t ∈ ts →
    ∀ (hint : TyS) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s → run K ρ φ hint t s = run K ρ φ' hint t s
  | [], t, h, _, _, _, _, _, _ => absurd h List.not_mem_nil
  | a :: as, t, h, hint, s, L, hφ, ht, hi => by
    rw [List.mem_cons] at h
    rcases h with e | h
    · rw [e] at ht ⊢; exact run_congrE hK a hint s L hφ ht hi
    · exact runAll_congrE hK as t h hint s L hφ ht hi

theorem runBinds_congrE (hK : ∀ n, (K.C.global n).2.label = none) (s : SState) (L : Nat → Prop)
    (hφ : ∀ l, L l → φ l = φ' l) (hi : RInv L s) (dcs : List DeclInfo) : ∀ (ds : List Term) (pre : List PBind),
    (∀ l, Term.anyAtomList (· == .loan l) ds = true → L l) →
    runBinds K ρ φ s dcs pre ds = runBinds K ρ φ' s dcs pre ds
  | [], _, _ => rfl
  | d :: ds, pre, ht => by
    have hds := fun pre' => runBinds_congrE hK s L hφ hi dcs ds pre' (fun l h => ht l (by simp [Term.anyAtomList, h]))
    have hd : (fun acc => run K ρ φ (.plain .err) d (extendBy s pre acc))
        = (fun acc => run K ρ φ' (.plain .err) d (extendBy s pre acc)) :=
      funext fun acc => run_congrE hK d _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) (rinv_extendBy hi pre acc)
    cases d with
    | ref A =>
      have hA : (fun acc => run K ρ φ (.plain .err) A (extendBy s pre acc))
          = (fun acc => run K ρ φ' (.plain .err) A (extendBy s pre acc)) :=
        funext fun acc => run_congrE hK A _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, Term.anyAtom, h]))
          (rinv_extendBy hi pre acc)
      simp only [runBinds, hA, hds]
    | _ => simp only [runBinds, hd, hds]

theorem runArgs_congrE (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (shape : Option (List PiParam × PiOut)) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runArgs K ρ φ stmt shape i earlier args s = runArgs K ρ φ' stmt shape i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runArgs]
    apply SM.bind_congr (SM.stmtIf_congr (run_congrE hK a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have hi₁ : RInv L s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · exact (run_rinv K ρ φ L hK a _ s s₁ r hi h1).1
      · exact hi
    apply SM.bind_congr (runArgs_congrE hK stmt shape as _ _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi₁)
    intro _ _ _; rfl

theorem runFields_congrE (hK : ∀ n, (K.C.global n).2.label = none) (stmt : Bool) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runFields K ρ φ stmt d ps c i earlier args s = runFields K ρ φ' stmt d ps c i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runFields]
    apply SM.bind_congr (SM.stmtIf_congr (run_congrE hK a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have hi₁ : RInv L s₁ := by
      rcases SM.stmtIf_some h1 with ⟨-, h1⟩ | ⟨-, rfl, -, -⟩
      · exact (run_rinv K ρ φ L hK a _ s s₁ r hi h1).1
      · exact hi
    apply SM.bind_congr (runFields_congrE hK stmt d ps c as _ _ s₁ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi₁)
    intro _ _ _; rfl

theorem runParams_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) :
    ∀ (args : List Term) (i : Nat) (earlier : List Sem) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomList (· == .loan l) args = true → L l) → RInv L s →
    runParams K ρ φ d i earlier args s = runParams K ρ φ' d i earlier args s
  | [], _, _, _, _, _, _, _ => rfl
  | a :: as, i, earlier, s, L, hφ, ht, hi => by
    simp only [runParams]
    apply SM.bind_congr (SM.onCopy_congr (run_congrE hK a _ s L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi))
    intro r s₁ h1
    have e := SM.onCopy_state h1
    subst e
    apply SM.bind_congr (runParams_congrE hK d as _ _ _ L hφ (fun l h => ht l (by simp [Term.anyAtomList, h])) hi)
    intro _ _ _; rfl

theorem runArm_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (arms : List (Hint × Term)) (hint : TyS)
    (c : Nat) (s : SState) (L : Nat → Prop), (∀ l, L l → φ l = φ' l) →
    (∀ l, Term.anyAtomArms (· == .loan l) arms = true → L l) → RInv L s →
    runArm K ρ φ hint c arms s = runArm K ρ φ' hint c arms s
  | [], _, _, _, _, _, _, _ => rfl
  | (_, t) :: rest, hint, c, s, L, hφ, ht, hi => by
    simp only [runArm]
    split
    · exact run_congrE hK t hint s L hφ (fun l h => ht l (by simp [Term.anyAtomArms, h])) hi
    · exact runArm_congrE hK rest hint (c - 1) s L hφ (fun l h => ht l (by simp [Term.anyAtomArms, h])) hi

theorem capsVals_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (vs : List Value),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) → capsVals K ρ φ vs = capsVals K ρ φ' vs
  | [], _ => rfl
  | v :: vs, hv => by
    simp only [capsVals]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomList, h])),
      capsVals_congrE hK vs (fun l h => hv l (by simp [Value.anyAtomList, h]))]

theorem capsTys_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (rd : List (DeclInfo × Value)),
    (∀ l, Value.anyAtomRd (· == .loan l) rd = true → φ l = φ' l) → capsTys K ρ φ rd = capsTys K ρ φ' rd
  | [], _ => rfl
  | (d, T) :: rest, hv => by
    simp only [capsTys]
    rw [meanV_congrE hK T _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomRd, h])),
      capsTys_congrE hK rest (fun l h => hv l (by simp [Value.anyAtomRd, h]))]

theorem meanFields_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) (ps : List Sem) (c : Nat) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) →
    meanFields K ρ φ d ps c i earlier vs = meanFields K ρ φ' d ps c i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanFields]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomList, h])),
      meanFields_congrE hK d ps c vs _ _ (fun l h => hv l (by simp [Value.anyAtomList, h]))]

theorem meanParams_congrE (hK : ∀ n, (K.C.global n).2.label = none) (d : IndDecl) :
    ∀ (vs : List Value) (i : Nat) (earlier : List Sem),
    (∀ l, Value.anyAtomList (· == .loan l) vs = true → φ l = φ' l) →
    meanParams K ρ φ d i earlier vs = meanParams K ρ φ' d i earlier vs
  | [], _, _, _ => rfl
  | v :: vs, i, earlier, hv => by
    simp only [meanParams]
    rw [meanV_congrE hK v _ (fun l h => hv l (by simp [Value.hasLoan] at h; simp [Value.anyAtomList, h])),
      meanParams_congrE hK d vs _ _ (fun l h => hv l (by simp [Value.anyAtomList, h]))]


theorem piShapeOf_congrE (hK : ∀ n, (K.C.global n).2.label = none) : ∀ (t : Term) (s : SState) (L : Nat → Prop),
    (∀ l, L l → φ l = φ' l) → (∀ l, t.anyAtom (· == .loan l) = true → L l) → RInv L s →
    piShapeOf K ρ φ s t = piShapeOf K ρ φ' s t
  | t, s, L, hφ, ht, hi => by
    cases t with
    | pi hs ds c =>
      have hbs := runBinds_congrE hK s L hφ hi (K.D.paramDecls (scopeOf s) ds) ds []
        (fun l h => ht l (by simp [Term.anyAtom, h]))
      have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run K ρ φ' (.plain .err) c (extendBy s bs acc) :=
        fun bs acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run K ρ φ' (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
        simp only [piShapeOf, hU, hbs]
      | _ => simp only [piShapeOf, hc, hbs]
    | fix self hs ds c dec body =>
      have hbs := runBinds_congrE hK s L hφ hi (K.D.paramDecls (scopeOf s) ds) ds []
        (fun l h => ht l (by simp [Term.anyAtom, h]))
      have hc : ∀ bs acc, run K ρ φ (.plain .err) c (extendBy s bs acc) = run K ρ φ' (.plain .err) c (extendBy s bs acc) :=
        fun bs acc => run_congrE hK c _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
      cases c with
      | ref U =>
        have hU : ∀ bs acc, run K ρ φ (.plain .err) U (extendBy s bs acc) = run K ρ φ' (.plain .err) U (extendBy s bs acc) :=
          fun bs acc => run_congrE hK U _ _ L hφ (fun l h => ht l (by simp [Term.anyAtom, h])) (rinv_extendBy hi bs acc)
        simp only [piShapeOf, hU, hbs]
      | _ => simp only [piShapeOf, hc, hbs]
    | _ => simp only [piShapeOf]

end

end

end Ochr.Meaning
