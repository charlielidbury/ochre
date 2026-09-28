import OchrMeta.GuardTerm

/-! # Lemma 1 for borrow-free programs: the machine on borrow-free states

The *borrow-free fragment*: no `&p` term, no parameter or result of type `&T`.  Run from a state
with no borrow anywhere, such a program never creates one (the only sources of borrows are `&p`,
the generic call state of a borrow parameter, and [Close] at a borrow result), so no loan is ever
live: [Access] never ends anything, [Drop] never complains, and a call never touches its caller's
frame.  This file proves these facts (`exec_bf`) and the structural half of Lemma 1 relative to the
invariant (`exec_total_bf`).  The recursive half is in `GuardSim.lean` / `GuardSimG.lean`. -/

namespace OchrMeta

mutual
def Term.noBorrow : Term → Bool
  | .borrow _ => false
  | .read _ | .zero | .unit => true
  | .assign _ t | .succ t | .erase t => t.noBorrow
  | .letIn _ t u | .seq t u | .pair t u => t.noBorrow && u.noBorrow
  | .mtch _ tz _ ts => tz.noBorrow && ts.noBorrow
  | .call _ args _ => Term.noBorrowList args
def Term.noBorrowList : List Term → Bool
  | [] => true
  | t :: ts => t.noBorrow && Term.noBorrowList ts
end

mutual
theorem Term.noBorrow_substVar (y : Var) (q : Place) : ∀ t : Term, (t.substVar y q).noBorrow = t.noBorrow
  | .read _ | .borrow _ | .zero | .unit => rfl
  | .assign _ t | .succ t | .erase t => by
    simp only [Term.substVar, Term.noBorrow, Term.noBorrow_substVar y q t]
  | .letIn x t u => by
    simp only [Term.substVar, Term.noBorrow, Term.noBorrow_substVar y q t]
    split <;> simp [Term.noBorrow_substVar y q u]
  | .seq t u | .pair t u => by
    simp only [Term.substVar, Term.noBorrow, Term.noBorrow_substVar y q t, Term.noBorrow_substVar y q u]
  | .mtch _ tz z ts => by
    simp only [Term.substVar, Term.noBorrow, Term.noBorrow_substVar y q tz]
    split <;> simp [Term.noBorrow_substVar y q ts]
  | .call _ args _ => by
    simp only [Term.substVar, Term.noBorrow, Term.noBorrowList_substVar y q args]
theorem Term.noBorrowList_substVar (y : Var) (q : Place) : ∀ ts : List Term,
    Term.noBorrowList (Term.substVarList y q ts) = Term.noBorrowList ts
  | [] => rfl
  | t :: ts => by
    simp only [Term.substVarList, Term.noBorrowList, Term.noBorrow_substVar y q t,
      Term.noBorrowList_substVar y q ts]
end

theorem Term.noBorrowList_iff : ∀ {ts : List Term}, Term.noBorrowList ts = true ↔ ∀ t ∈ ts, t.noBorrow = true
  | [] => by simp [Term.noBorrowList]
  | t :: ts => by simp [Term.noBorrowList, Term.noBorrowList_iff (ts := ts)]

def Ty.isRef : Ty → Bool
  | .ref _ => true
  | _ => false

/-- A borrow-free definition: no borrow parameter, no borrow result, no `&p` in the body. -/
structure FunDef.BF (d : FunDef) : Prop where
  params : ∀ p ∈ d.params, p.2.isRef = false
  ret : d.ret.isRef = false
  body : ∀ b, d.body = some b → b.noBorrow = true

def Prog.BF (P : Prog) : Prop := ∀ f d, P.find f = some d → d.BF

/-! ## No borrow, no live loan -/

theorem Frame.holds_of_nb_g {F : Frame} (h : F.nb = 0) (l : Nat) : F.holds l = false := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨x, v⟩ := b
    simp only [Frame.nb] at h
    simp only [Frame.holds, List.any_cons] at ih ⊢
    rw [ih (by omega)]
    cases v <;> simp_all [Val.isBorrowOf, Val.nb]

theorem Env.holds_of_nb {Ω : Env} (h : Ω.nb = 0) (l : Nat) : Ω.holds l = false := by
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.nb] at h
    simp only [Env.holds, List.any_cons] at ih ⊢
    rw [ih (by omega), Frame.holds_of_nb_g (by omega)]
    rfl

theorem St.live_of_nb {s : St} (h : s.env.nb = 0) : s.live = fun _ => false := by
  funext l; exact Env.holds_of_nb h l

theorem Val.firstLive_false (v : Val) : v.firstLive (fun _ => false) = none := by
  induction v <;> simp_all [Val.firstLive]

/-- The pure walk of a path: a projection per step, no loan ends. -/
def Val.getR : Val → List Proj → StepRes
  | v, [] => .ok v
  | v, pr :: ps => match pr.step v with
    | .ok w => w.getR ps
    | .stuck => .stuck
    | .err => .err

def StepRes.toWalk : StepRes → WalkRes
  | .ok c => .done c
  | .stuck => .stuck
  | .err => .err

theorem walk_false (deep : Bool) : ∀ (v : Val) (π : List Proj),
    walk (fun _ => false) deep v π = (v.getR π).toWalk
  | v, [] => by
    simp only [walk, headLoan, Val.getR, StepRes.toWalk]
    cases v <;> simp [Val.firstLive_false]
  | v, pr :: ps => by
    have hh : headLoan (fun _ => false) v = none := by cases v <;> simp [headLoan]
    simp only [walk, hh, Val.getR]
    cases pr.step v with
    | ok w => exact walk_false deep w ps
    | stuck => rfl
    | err => rfl

/-- [Access] on a state without borrows: a lookup and a pure walk; the state is unchanged. -/
theorem access_nb {s : St} (h : s.env.nb = 0) (deep : Bool) (x : Var) (π : List Proj) :
    access deep x π s = match s.lookup x with
      | none => .err
      | some v => match v.getR π with
        | .ok c => .ok s c
        | .stuck => .stuck
        | .err => .err := by
  rw [access]
  cases s.lookup x with
  | none => rfl
  | some v =>
    simp only [St.live_of_nb h, walk_false]
    cases v.getR π <;> rfl

/-! ## Bounds: no borrow, abstract ids below `N` -/

def Frame.absIds (F : Frame) : List Nat := F.flatMap fun b => b.2.absIds

/-- A borrow-free value whose abstract ids are below `N`. -/
def BFVal (N : Nat) (v : Val) : Prop := v.nb = 0 ∧ ∀ a ∈ v.absIds, a < N

/-- The borrow-free invariant of a state `⟨F :: Ω, k⟩`: no borrow anywhere, and the abstract ids of
the top frame below `N`. -/
structure BFSt (N : Nat) (F : Frame) (Ω : Env) : Prop where
  top : F.nb = 0
  rest : Ω.nb = 0
  abs : ∀ a ∈ Frame.absIds F, a < N

theorem BFSt.env_nb {N : Nat} {F : Frame} {Ω : Env} (h : BFSt N F Ω) : Env.nb (F :: Ω) = 0 := by
  simp only [Env.nb, h.top, h.rest]

theorem Frame.nb_cons (x : Var) (v : Val) (F : Frame) : Frame.nb ((x, v) :: F) = v.nb + F.nb := rfl

theorem Frame.bf_cons {N : Nat} {x : Var} {v : Val} {F : Frame} :
    (Frame.nb ((x, v) :: F) = 0 ∧ ∀ a ∈ Frame.absIds ((x, v) :: F), a < N) ↔
      (BFVal N v ∧ F.nb = 0 ∧ ∀ a ∈ Frame.absIds F, a < N) := by
  simp only [Frame.nb_cons, Frame.absIds, List.flatMap_cons, List.mem_append, BFVal]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, fun a ha => h2 a (Or.inl ha)⟩, by omega, fun a ha => h2 a (Or.inr ha)⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by omega, fun a ha => ha.elim (h2 a) (h4 a)⟩

theorem BFSt.cons {N : Nat} {F : Frame} {Ω : Env} (h : BFSt N F Ω) {x : Var} {v : Val} (hv : BFVal N v) :
    BFSt N ((x, v) :: F) Ω :=
  ⟨(Frame.bf_cons.mpr ⟨hv, h.top, h.abs⟩).1, h.rest, (Frame.bf_cons.mpr ⟨hv, h.top, h.abs⟩).2⟩

theorem Proj.step_ok {pr : Proj} {v w : Val} (h : pr.step v = .ok w) :
    w.nb ≤ v.nb ∧ ∀ a ∈ w.absIds, a ∈ v.absIds := by
  cases pr <;> cases v <;> simp_all [Proj.step, Val.isNeutral, Val.nb, Val.absIds] <;>
    (try split at h) <;> (try simp_all) <;> (try (cases h; simp; omega)) <;>
    (try (cases h; exact ⟨by omega, fun a ha => Or.inl ha⟩)) <;> (try (cases h; exact ⟨by omega, fun a ha => Or.inr ha⟩))

theorem Val.getR_ok : ∀ {v : Val} {π : List Proj} {c : Val}, v.getR π = .ok c →
    c.nb ≤ v.nb ∧ ∀ a ∈ c.absIds, a ∈ v.absIds
  | v, [], c, h => by simp only [Val.getR, StepRes.ok.injEq] at h; subst h; exact ⟨Nat.le_refl _, fun _ h => h⟩
  | v, pr :: ps, c, h => by
    simp only [Val.getR] at h
    split at h
    · rename_i w hw
      obtain ⟨h1, h2⟩ := Proj.step_ok hw
      obtain ⟨h3, h4⟩ := Val.getR_ok h
      exact ⟨by omega, fun a ha => h2 a (h4 a ha)⟩
    · cases h
    · cases h

theorem Proj.put_some {pr : Proj} {v w new v' : Val} (hs : pr.step v = .ok w) (h : pr.put v new = some v') :
    v'.nb + w.nb = v.nb + new.nb ∧ ∀ a ∈ v'.absIds, a ∈ v.absIds ∨ a ∈ new.absIds := by
  cases pr <;> cases v <;> simp_all [Proj.step, Proj.put, Val.isNeutral] <;> (try split at hs) <;>
    (try simp_all) <;> subst_vars <;> simp [Val.nb, Val.absIds] <;>
    exact ⟨by omega, by intro a ha; first | simp [ha] | (rcases ha with ha | ha <;> simp [ha])⟩

theorem Val.set_some : ∀ {v : Val} {π : List Proj} {new v' : Val}, v.set π new = some v' →
    v'.nb ≤ v.nb + new.nb ∧ ∀ a ∈ v'.absIds, a ∈ v.absIds ∨ a ∈ new.absIds
  | v, [], new, v', h => by
    simp only [Val.set, Option.some.injEq] at h; subst h; exact ⟨by omega, fun a ha => Or.inr ha⟩
  | v, pr :: ps, new, v', h => by
    simp only [Val.set] at h
    split at h
    · rename_i w hw
      obtain ⟨w', hw', hput⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨h1, h2⟩ := Val.set_some hw'
      obtain ⟨h3, h4⟩ := Proj.put_some hw hput
      obtain ⟨h5, h6⟩ := Proj.step_ok hw
      refine ⟨by omega, fun a ha => ?_⟩
      rcases h4 a ha with h | h
      · exact Or.inl h
      · rcases h2 a h with h | h
        · exact Or.inl (h6 a h)
        · exact Or.inr h
    · cases h

theorem Frame.lookup_mem {F : Frame} {x : Var} {v : Val} (h : F.lookup x = some v) : (x, v) ∈ F := by
  induction F with
  | nil => simp at h
  | cons b F ih =>
    obtain ⟨y, w⟩ := b
    simp only [List.lookup] at h
    split at h
    · rename_i hxy; simp only [Option.some.injEq] at h; subst h
      simp only [beq_iff_eq] at hxy; subst hxy; simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem Frame.mem_bf {N : Nat} {F : Frame} (h0 : F.nb = 0) (ha : ∀ a ∈ Frame.absIds F, a < N)
    {b : Var × Val} (hb : b ∈ F) : BFVal N b.2 := by
  induction F with
  | nil => simp at hb
  | cons c F ih =>
    obtain ⟨y, w⟩ := c
    have := Frame.bf_cons.mp ⟨h0, ha⟩
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact this.1
    · exact ih this.2.1 this.2.2 hb

theorem Frame.set_bf {N : Nat} {x : Var} {v : Val} (hv : BFVal N v) : ∀ {F : Frame},
    F.nb = 0 → (∀ a ∈ Frame.absIds F, a < N) → (F.set x v).nb = 0 ∧ ∀ a ∈ Frame.absIds (F.set x v), a < N
  | [], _, _ => by simp [Frame.set, Frame.nb, Frame.absIds]
  | (y, w) :: F, h0, ha => by
    have hF := Frame.bf_cons.mp ⟨h0, ha⟩
    simp only [Frame.set]
    split
    · exact Frame.bf_cons.mpr ⟨hv, hF.2⟩
    · have := Frame.set_bf (x := x) hv hF.2.1 hF.2.2
      exact Frame.bf_cons.mpr ⟨hF.1, this⟩

theorem Frame.remove_bf {N : Nat} {x : Var} : ∀ {F F' : Frame} {v : Val},
    F.nb = 0 → (∀ a ∈ Frame.absIds F, a < N) → F.remove x = some (v, F') →
    BFVal N v ∧ F'.nb = 0 ∧ ∀ a ∈ Frame.absIds F', a < N
  | [], _, _, _, _, h => by simp [Frame.remove] at h
  | (y, w) :: F, F', v, h0, ha, h => by
    have hF := Frame.bf_cons.mp ⟨h0, ha⟩
    simp only [Frame.remove] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hF
    · obtain ⟨⟨v', F''⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, h2, h3⟩ := Frame.remove_bf hF.2.1 hF.2.2 hr
      exact ⟨h1, Frame.bf_cons.mpr ⟨hF.1, h2, h3⟩⟩

theorem Val.isBorrowOf_of_nb {v : Val} (h : v.nb = 0) (l : Nat) : v.isBorrowOf l = false := by
  cases v <;> simp_all [Val.isBorrowOf, Val.nb]

/-- [Drop] on a borrow-free state is a no-op. -/
theorem dropVal_bf {extra v : Val} {s : St} (hs : s.env.nb = 0) (he : extra.nb = 0) (hv : v.nb = 0) :
    dropVal extra v s = some s := by
  have hl : (fun l => s.live l || extra.isBorrowOf l) = fun _ => false := by
    funext l; simp [St.live_of_nb hs, Val.isBorrowOf_of_nb he]
  unfold dropVal hasLive
  cases v with
  | borrow l w => simp [Val.nb] at hv
  | _ => simp [hl, Val.firstLive_false]

theorem popFrameN_bf {extra : Val} (he : extra.nb = 0) : ∀ (F : Frame) (Ω : Env) (k : Nat),
    Env.nb (F :: Ω) = 0 → popFrameN extra F.length ⟨F :: Ω, k⟩ = some ⟨Ω, k⟩
  | [], Ω, k, _ => rfl
  | (x, c) :: F, Ω, k, h => by
    simp only [Env.nb, Frame.nb_cons] at h
    simp only [List.length_cons, popFrameN]
    rw [dropVal_bf (by simp only [Env.nb]; omega) he (by omega)]
    exact popFrameN_bf he F Ω k (by simp only [Env.nb]; omega)

theorem popFrame_bf {extra : Val} (he : extra.nb = 0) (F : Frame) (Ω : Env) (k : Nat)
    (h : Env.nb (F :: Ω) = 0) : popFrame extra ⟨F :: Ω, k⟩ = some ⟨Ω, k⟩ :=
  popFrameN_bf he F Ω k h

theorem sealArgs_noref : ∀ (i : Nat) (ps : List (Var × Ty)) (ws : List Val) {as : List Val}
    {ls : List (Nat × Nat)}, (∀ p ∈ ps, p.2.isRef = false) → sealArgs i ps ws = some (as, ls) →
    as = ws ∧ ls = []
  | _, [], [], _, _, _, h => by simp [sealArgs] at h; exact ⟨h.1, h.2⟩
  | _, [], _ :: _, _, _, _, h => by simp [sealArgs] at h
  | _, (_, .ref _) :: _, _, _, _, hp, _ => by simp [Ty.isRef] at hp
  | i, (x, .nat) :: ps, w :: ws, as, ls, hp, h
  | i, (x, .unit) :: ps, w :: ws, as, ls, hp, h
  | i, (x, .pair _ _) :: ps, w :: ws, as, ls, hp, h
  | i, (x, .prop) :: ps, w :: ws, as, ls, hp, h => by
    simp only [sealArgs] at h
    obtain ⟨⟨as', ls'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := sealArgs_noref (i + 1) ps ws (fun p hp' => hp p (List.mem_cons_of_mem _ hp')) h1
    exact ⟨rfl, rfl⟩
  | _, (_, .nat) :: _, [], _, _, _, h | _, (_, .unit) :: _, [], _, _, _, h
  | _, (_, .pair _ _) :: _, [], _, _, _, h | _, (_, .prop) :: _, [], _, _, _, h => by simp [sealArgs] at h

theorem Val.nb_ofList : ∀ {ws : List Val}, (∀ w ∈ ws, w.nb = 0) → (Val.ofList ws).nb = 0
  | [], _ => rfl
  | w :: ws, h => by
    have := Val.nb_ofList (ws := ws) (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [Val.ofList, Val.nb, h w (by simp), this]

theorem Val.absIds_ofList : ∀ {ws : List Val} {a : Nat}, a ∈ (Val.ofList ws).absIds → ∃ w ∈ ws, a ∈ w.absIds
  | [], _, h => by simp [Val.ofList, Val.absIds] at h
  | w :: ws, a, h => by
    simp only [Val.ofList, Val.absIds, List.mem_append] at h
    rcases h with h | h
    · exact ⟨w, by simp, h⟩
    · obtain ⟨w', hw', h'⟩ := Val.absIds_ofList h; exact ⟨w', by simp [hw'], h'⟩

/-- [Close] of a borrow-free definition: the state is unchanged, the result is `()` or a sealed
program over the arguments. -/
theorem closeCall_bf {f : String} {d : FunDef} (hd : d.BF) {ws : List Val} {s s' : St} {v : Val}
    (h : closeCall f d ws s = .ok s' v) :
    s' = s ∧ (v = .unit ∨ ∃ k, v = .sealed f (Val.ofList ws) k .unit) := by
  unfold closeCall at h
  split at h
  · cases h
  · rename_i as ls hsa
    obtain ⟨rfl, rfl⟩ := sealArgs_noref 0 d.params ws hd.params hsa
    simp only at h
    split at h
    · cases h
    · have hr := hd.ret
      split at h
      · rename_i t ht; rw [ht] at hr; simp [Ty.isRef] at hr
      · simp only [List.map_nil, fillLoans] at h; cases h; exact ⟨rfl, Or.inl rfl⟩
      · simp only [List.map_nil, fillLoans] at h; cases h; exact ⟨rfl, Or.inr ⟨_, rfl⟩⟩

/-! ## The invariant: a borrow-free run changes only its top frame -/

/-- An evaluator that keeps the borrow-free invariant: from `⟨F :: Ω, k⟩` it only changes `F`. -/
def EvBF (ev : St → Term → Res) : Prop :=
  ∀ (N : Nat) (F : Frame) (Ω : Env) (k : Nat) (t : Term) (s' : St) (v : Val),
    t.noBorrow = true → BFSt N F Ω → ev ⟨F :: Ω, k⟩ t = .ok s' v →
    ∃ F', s' = ⟨F' :: Ω, k⟩ ∧ BFSt N F' Ω ∧ BFVal N v

theorem unbind_bf {N : Nat} {x : Var} {F : Frame} {Ω : Env} {k : Nat} {v : Val} {s' : St}
    (hs : BFSt N F Ω) (h : St.unbind x ⟨F :: Ω, k⟩ = some (v, s')) :
    ∃ F', s' = ⟨F' :: Ω, k⟩ ∧ BFSt N F' Ω ∧ BFVal N v := by
  simp only [St.unbind] at h
  obtain ⟨⟨v', F'⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨h1, h2, h3⟩ := Frame.remove_bf hs.top hs.abs hr
  exact ⟨F', rfl, ⟨h2, hs.rest, h3⟩, h1⟩

theorem execArgs_bf {ev : St → Term → Res} (hev : EvBF ev) {N : Nat} {Ω : Env} {k : Nat} :
    ∀ (args : List Term) (i : Nat) (F : Frame) (s' : St) (v : Val),
      (∀ a ∈ args, a.noBorrow = true) → BFSt N F Ω → execArgs ev i ⟨F :: Ω, k⟩ args = .ok s' v →
      ∃ F', s' = ⟨F' :: Ω, k⟩ ∧ BFSt N F' Ω
  | [], i, F, s', v, _, hs, h => by simp only [execArgs, Res.ok.injEq] at h; exact ⟨F, h.1.symm, hs⟩
  | a :: as, i, F, s', v, ha, hs, h => by
    simp only [execArgs] at h
    cases h1 : ev ⟨F :: Ω, k⟩ a with
    | ok s1 w =>
      rw [h1, Res.bind_ok] at h
      obtain ⟨F1, rfl, hs1, hw⟩ := hev N F Ω k a s1 w (ha a (by simp)) hs h1
      exact execArgs_bf hev as (i + 1) ((Var.tmp i, w) :: F1) s' v (fun b hb => ha b (by simp [hb]))
        (hs1.cons hw) h
    | _ => rw [h1] at h; cases h

theorem takeTemps_bf {N : Nat} {Ω : Env} {k : Nat} : ∀ (is : List Nat) (F : Frame) (ws : List Val) (s' : St),
    BFSt N F Ω → takeTemps is ⟨F :: Ω, k⟩ = some (ws, s') →
    ∃ F', s' = ⟨F' :: Ω, k⟩ ∧ BFSt N F' Ω ∧ ∀ w ∈ ws, BFVal N w
  | [], F, ws, s', hs, h => by
    simp only [takeTemps, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨F, rfl, hs, by simp⟩
  | i :: is, F, ws, s', hs, h => by
    simp only [takeTemps] at h
    obtain ⟨⟨v, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨F1, rfl, hs1, hv⟩ := unbind_bf hs h1
    obtain ⟨⟨vs, s2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
    simp only [Prod.mk.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
    obtain ⟨F2, rfl, hs2, hvs⟩ := takeTemps_bf is F1 vs s2 hs1 h3
    refine ⟨F2, rfl, hs2, fun w hw => ?_⟩
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact hvs w hw

theorem paramFrame_bf {N : Nat} (d : FunDef) : ∀ (ps : List Var) (ws : List Val), (∀ w ∈ ws, BFVal N w) →
    Frame.nb (ps.zip ws) = 0 ∧ ∀ a ∈ Frame.absIds (ps.zip ws), a < N
  | [], _, _ => by simp [Frame.nb, Frame.absIds]
  | _ :: _, [], _ => by simp [Frame.nb, Frame.absIds]
  | x :: ps, w :: ws, h => by
    simp only [List.zip_cons_cons]
    exact Frame.bf_cons.mpr ⟨h w (by simp), paramFrame_bf d ps ws (fun v hv => h v (by simp [hv]))⟩

/-- A borrow-free call returns to exactly the caller's state. -/
theorem callWith_bf {ev : St → Term → Res} (hev : EvBF ev) {cc : Bool} {h : String} {d : FunDef}
    (hd : d.BF) {N : Nat} {F : Frame} {Ω : Env} {k : Nat} {ws : List Val} {s' : St} {v : Val}
    (hs : BFSt N F Ω) (hws : ∀ w ∈ ws, BFVal N w) (hc : callWith ev cc h d ws ⟨F :: Ω, k⟩ = .ok s' v) :
    s' = ⟨F :: Ω, k⟩ ∧ BFVal N v := by
  have hclose : closeCall h d ws ⟨F :: Ω, k⟩ = .ok s' v → s' = ⟨F :: Ω, k⟩ ∧ BFVal N v := by
    intro hc'
    obtain ⟨rfl, hv⟩ := closeCall_bf hd hc'
    refine ⟨rfl, ?_⟩
    rcases hv with rfl | ⟨k', rfl⟩
    · exact ⟨rfl, by simp [Val.absIds]⟩
    · refine ⟨by simp [Val.nb, Val.nb_ofList (fun w hw => (hws w hw).1)], fun a ha => ?_⟩
      simp only [Val.absIds, List.mem_append] at ha
      rcases ha with ha | ha
      · obtain ⟨w, hw, ha⟩ := Val.absIds_ofList ha; exact (hws w hw).2 a ha
      · simp at ha
  unfold callWith at hc
  split at hc
  · split at hc
    · exact hclose hc
    · cases hc
  · rename_i b hb
    split at hc
    · have hp := paramFrame_bf (N := N) d (d.params.map Prod.fst) ws hws
      split at hc
      · rename_i s1 v1 hr
        obtain ⟨F1, rfl, hs1, hv1⟩ := hev N (paramFrame d ws) (F :: Ω) k b s1 v1 (hd.body b hb)
          ⟨hp.1, hs.env_nb, hp.2⟩ hr
        rw [popFrame_bf hv1.1 F1 (F :: Ω) k (by simp only [Env.nb, hs1.top, hs.top, hs.rest])] at hc
        simp only [Res.ok.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
        exact ⟨rfl, hv1⟩
      · split at hc
        · exact hclose hc
        · cases hc
      · cases hc
      · cases hc
    · cases hc

theorem access_bf {N : Nat} {F : Frame} {Ω : Env} {k : Nat} {deep : Bool} {x : Var} {π : List Proj}
    {s' : St} {c : Val} (hs : BFSt N F Ω) (h : access deep x π ⟨F :: Ω, k⟩ = .ok s' c) :
    s' = ⟨F :: Ω, k⟩ ∧ BFVal N c := by
  rw [access_nb hs.env_nb] at h
  simp only [St.lookup, List.head?_cons, Option.bind_some] at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · rename_i c' hc
      simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hv' := Frame.mem_bf hs.top hs.abs (Frame.lookup_mem hv)
      obtain ⟨h1, h2⟩ := Val.getR_ok hc
      exact ⟨rfl, Nat.eq_zero_of_le_zero (hv'.1 ▸ h1), fun a ha => hv'.2 a (h2 a ha)⟩
    · cases h
    · cases h

theorem setPlace_bf {N : Nat} {F : Frame} {Ω : Env} {k : Nat} {x : Var} {π : List Proj} {v : Val}
    {s' : St} (hs : BFSt N F Ω) (hv : BFVal N v) (h : St.setPlace x π v ⟨F :: Ω, k⟩ = some s') :
    ∃ F', s' = ⟨F' :: Ω, k⟩ ∧ BFSt N F' Ω := by
  simp only [St.setPlace, St.lookup, List.head?_cons, Option.bind_some] at h
  obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h1
  have hcv := Frame.mem_bf hs.top hs.abs (Frame.lookup_mem hc)
  obtain ⟨h2, h3⟩ := Val.set_some hc'
  have e1 : c.nb = 0 := hcv.1
  have e2 : v.nb = 0 := hv.1
  have hbf : BFVal N c' := ⟨by omega,
    fun a ha => (h3 a ha).elim (hcv.2 a) (hv.2 a)⟩
  have := Frame.set_bf (x := x) hbf hs.top hs.abs
  exact ⟨F.set x c', rfl, this.1, hs.rest, this.2⟩

/-- **The borrow-free invariant**: a run of a borrow-free term in a borrow-free program, from a
borrow-free state, changes only the top frame, creates no borrow and invents no abstract value. -/
theorem exec_bf {P : Prog} (hP : P.BF) : ∀ n, EvBF (exec P n) := by
  intro n
  induction n with
  | zero => intro N F Ω k t s' v _ _ h; simp [exec] at h
  | succ n ih =>
    intro N F Ω k t s' v ht hs h
    cases t with
    | read p =>
      simp only [exec] at h
      cases ha : access true p.root p.path ⟨F :: Ω, k⟩ with
      | ok s1 c =>
        rw [ha, Res.bind_ok] at h
        obtain ⟨rfl, hc⟩ := access_bf hs ha
        split at h
        · cases h
        · simp [BFVal, Val.nb] at hc
        · simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨F, rfl, hs, hc⟩
      | _ => rw [ha] at h; cases h
    | borrow p => simp [Term.noBorrow] at ht
    | assign p t =>
      simp only [exec] at h
      simp only [Term.noBorrow] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F1, rfl, hs1, hv1⟩ := ih N F Ω k t s1 v1 ht hs h1
        cases ha : access true p.root p.path ⟨F1 :: Ω, k⟩ with
        | ok s2 c =>
          rw [ha, Res.bind_ok] at h
          obtain ⟨rfl, hc⟩ := access_bf hs1 ha
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i s3 hs3
              obtain ⟨F3, rfl, hbf3⟩ := setPlace_bf hs1 hv1 hs3
              rw [dropVal_bf hbf3.env_nb rfl hc.1] at h
              simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              exact ⟨F3, rfl, hbf3, rfl, by simp [Val.absIds]⟩
        | _ => rw [ha] at h; cases h
      | _ => rw [h1] at h; cases h
    | letIn x t u =>
      simp only [exec] at h
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F1, rfl, hs1, hv1⟩ := ih N F Ω k t s1 v1 ht.1 hs h1
        cases h2 : exec P n ⟨((x, v1) :: F1) :: Ω, k⟩ u with
        | ok s2 w =>
          have e : St.bind x v1 ⟨F1 :: Ω, k⟩ = ⟨((x, v1) :: F1) :: Ω, k⟩ := rfl
          rw [e, h2, Res.bind_ok] at h
          obtain ⟨F2, rfl, hs2, hw⟩ := ih N _ Ω k u s2 w ht.2 (hs1.cons hv1) h2
          split at h
          · cases h
          · rename_i c s3 hu
            obtain ⟨F3, rfl, hs3, hc⟩ := unbind_bf hs2 hu
            rw [dropVal_bf hs3.env_nb hw.1 hc.1] at h
            simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            exact ⟨F3, rfl, hs3, hw⟩
        | _ =>
          have e : St.bind x v1 ⟨F1 :: Ω, k⟩ = ⟨((x, v1) :: F1) :: Ω, k⟩ := rfl
          rw [e, h2] at h; cases h
      | _ => rw [h1] at h; cases h
    | seq t u =>
      simp only [exec] at h
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F1, rfl, hs1, hv1⟩ := ih N F Ω k t s1 v1 ht.1 hs h1
        rw [dropVal_bf hs1.env_nb rfl hv1.1] at h
        exact ih N F1 Ω k u s' v ht.2 hs1 h
      | _ => rw [h1] at h; cases h
    | zero => simp only [exec, Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨F, rfl, hs, rfl, by simp [Val.absIds]⟩
    | unit => simp only [exec, Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨F, rfl, hs, rfl, by simp [Val.absIds]⟩
    | erase t => simp only [exec, Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨F, rfl, hs, rfl, by simp [Val.absIds]⟩
    | succ t =>
      simp only [exec] at h
      simp only [Term.noBorrow] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F1, rfl, hs1, hv1⟩ := ih N F Ω k t s1 v1 ht hs h1
        split at h
        · simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨F1, rfl, hs1, by simp [Val.nb, hv1.1], by simpa [Val.absIds] using hv1.2⟩
        · cases h
      | _ => rw [h1] at h; cases h
    | pair t u =>
      simp only [exec] at h
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F1, rfl, hs1, hv1⟩ := ih N F Ω k t s1 v1 ht.1 hs h1
        cases h2 : exec P n ⟨F1 :: Ω, k⟩ u with
        | ok s2 v2 =>
          rw [h2, Res.bind_ok] at h
          obtain ⟨F2, rfl, hs2, hv2⟩ := ih N F1 Ω k u s2 v2 ht.2 hs1 h2
          split at h
          · simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨F2, rfl, hs2, by simp [Val.nb, hv1.1, hv2.1], fun a ha => ?_⟩
            simp only [Val.absIds, List.mem_append] at ha
            exact ha.elim (hv1.2 a) (hv2.2 a)
          · cases h
        | _ => rw [h2] at h; cases h
      | _ => rw [h1] at h; cases h
    | mtch p tz y ts =>
      simp only [exec] at h
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases ha : access false p.root p.path ⟨F :: Ω, k⟩ with
      | ok s1 c =>
        rw [ha, Res.bind_ok] at h
        obtain ⟨rfl, _⟩ := access_bf hs ha
        split at h
        · exact ih N F Ω k tz s' v ht.1 hs h
        · exact ih N F Ω k _ s' v (by rw [Term.noBorrow_substVar]; exact ht.2) hs h
        · split at h <;> cases h
      | _ => rw [ha] at h; cases h
    | call f args cc =>
      simp only [exec] at h
      cases hf : P.find f with
      | none => rw [hf] at h; cases h
      | some d =>
        rw [hf] at h
        simp only at h
        split at h
        · simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨F, rfl, hs, rfl, by simp [Val.absIds]⟩
        · cases h1 : execArgs (exec P n) 0 ⟨F :: Ω, k⟩ args with
          | ok s1 v1 =>
            rw [h1, Res.bind_ok] at h
            obtain ⟨F1, rfl, hs1⟩ := execArgs_bf ih args 0 F s1 v1
              (Term.noBorrowList_iff.mp (by simpa [Term.noBorrow] using ht)) hs h1
            split at h
            · cases h
            · rename_i ws s2 htt
              obtain ⟨F2, rfl, hs2, hws⟩ := takeTemps_bf _ F1 ws s2 hs1 htt
              obtain ⟨rfl, hv⟩ := callWith_bf ih (hP f d hf) hs2 hws h
              exact ⟨F2, rfl, hs2, hv⟩
          | _ => rw [h1] at h; cases h

/-! ## The structural half, relative to the invariant -/

theorem Stab.bind' {F : Nat → Res} {G : Nat → St → Val → Res} (hF : Stab F)
    (hG : ∀ n s v, F n = .ok s v → Stab (fun m => G m s v)) : Stab (fun n => (F n).bind (G n)) := by
  obtain ⟨n, r, hr, hn⟩ := hF
  cases r with
  | ok s v =>
    obtain ⟨n', r', hr', hn'⟩ := hG n s v (hn n (Nat.le_refl n))
    refine ⟨max n n', r', hr', fun m hm => ?_⟩
    show (F m).bind (G m) = r'
    rw [hn m (by omega), Res.bind_ok]; exact hn' m (by omega)
  | oof => exact absurd rfl hr
  | stuck => exact ⟨n, .stuck, by simp, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩
  | err => exact ⟨n, .err, by simp, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩

/-- A call to `h` at `ws` terminates from every borrow-free call point. -/
def CallTermBF (P : Prog) (h : String) (ws : List Val) : Prop :=
  ∀ d, P.find h = some d → ∀ (cc : Bool) (N : Nat) (F : Frame) (Ω : Env) (k : Nat),
    BFSt N F Ω → (∀ w ∈ ws, BFVal N w) → ∃ n, callWith (exec P n) cc h d ws ⟨F :: Ω, k⟩ ≠ .oof

theorem execArgs_stab_bf {P : Prog} (hP : P.BF) {N : Nat} {Ω : Env} {k : Nat} : ∀ (args : List Term),
    (∀ a ∈ args, a.noBorrow = true) →
    (∀ a ∈ args, ∀ F, BFSt N F Ω → ∃ n, exec P n ⟨F :: Ω, k⟩ a ≠ .oof) →
    ∀ i F, BFSt N F Ω → Stab (fun n => execArgs (exec P n) i ⟨F :: Ω, k⟩ args)
  | [], _, _, i, F, _ => Stab.of_eq (fun _ => rfl) (by simp)
  | a :: as, hb, h, i, F, hs => by
    simp only [execArgs]
    refine Stab.bind' (Stab.ofExec (h a (by simp) F hs)) fun n s v hr => ?_
    obtain ⟨F1, rfl, hs1, hv⟩ := exec_bf hP n N F Ω k a s v (hb a (by simp)) hs hr
    exact execArgs_stab_bf hP as (fun b hb' => hb b (by simp [hb'])) (fun b hb' => h b (by simp [hb']))
      (i + 1) _ (hs1.cons hv)

theorem exec_total_bf {P : Prog} (hP : P.BF) : ∀ M (t : Term), t.sz < M → t.noBorrow = true →
    (∀ h ∈ t.calls, ∀ ws, CallTermBF P h ws) →
    ∀ N F Ω k, BFSt N F Ω → ∃ n, exec P n ⟨F :: Ω, k⟩ t ≠ .oof := by
  intro M
  induction M with
  | zero => intro t h; omega
  | succ M ih =>
    intro t hsz hb hc N F Ω k hs
    apply Stab.execSucc
    have sub : ∀ t' : Term, t'.sz < t.sz → t'.noBorrow = true → (∀ h ∈ t'.calls, h ∈ t.calls) →
        ∀ F, BFSt N F Ω → Stab (fun n => exec P n ⟨F :: Ω, k⟩ t') :=
      fun t' h1 hb' h2 F hs => Stab.ofExec (ih t' (by omega) hb' (fun h hh => hc h (h2 h hh)) N F Ω k hs)
    cases t with
    | read p =>
      simp only [exec]
      refine Stab.of_eq (fun _ => rfl) ?_
      refine Res.bind_ne_oof (access_ne_oof' _ _ _ _) fun s c => ?_
      split
      · simp
      · split <;> simp
      · simp
    | borrow p => simp [Term.noBorrow] at hb
    | assign p t =>
      simp only [exec]
      simp only [Term.noBorrow] at hb
      refine Stab.bind (sub t (by simp [Term.sz]) hb (fun h hh => by simp [Term.calls, hh]) F hs)
        fun s v => Stab.of_eq (fun _ => rfl) ?_
      refine Res.bind_ne_oof (access_ne_oof' _ _ _ _) fun s c => ?_
      split
      · simp
      · split
        · simp
        · split <;> simp
    | letIn x t u =>
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at hb
      refine Stab.bind' (sub t (by simp [Term.sz]; omega) hb.1 (fun h hh => by simp [Term.calls, hh]) F hs)
        fun n s v hr => ?_
      obtain ⟨F1, rfl, hs1, hv⟩ := exec_bf hP n N F Ω k t s v hb.1 hs hr
      refine Stab.bind (sub u (by simp [Term.sz]; omega) hb.2 (fun h hh => by simp [Term.calls, hh]) _
        (hs1.cons (x := x) hv)) fun s w => ?_
      refine Stab.of_eq (fun _ => rfl) ?_
      split
      · simp
      · split <;> simp
    | seq t u =>
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at hb
      refine Stab.bind' (sub t (by simp [Term.sz]; omega) hb.1 (fun h hh => by simp [Term.calls, hh]) F hs)
        fun n s v hr => ?_
      obtain ⟨F1, rfl, hs1, hv⟩ := exec_bf hP n N F Ω k t s v hb.1 hs hr
      rw [dropVal_bf hs1.env_nb rfl hv.1]
      exact sub u (by simp [Term.sz]; omega) hb.2 (fun h hh => by simp [Term.calls, hh]) F1 hs1
    | zero => exact Stab.of_eq (fun _ => rfl) (by simp)
    | unit => exact Stab.of_eq (fun _ => rfl) (by simp)
    | erase t => exact Stab.of_eq (fun _ => rfl) (by simp)
    | succ t =>
      simp only [exec]
      simp only [Term.noBorrow] at hb
      refine Stab.bind (sub t (by simp [Term.sz]) hb (fun h hh => by simp [Term.calls, hh]) F hs) fun s v => ?_
      exact Stab.of_eq (fun _ => rfl) (by split <;> simp)
    | pair t u =>
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at hb
      refine Stab.bind' (sub t (by simp [Term.sz]; omega) hb.1 (fun h hh => by simp [Term.calls, hh]) F hs)
        fun n s v hr => ?_
      obtain ⟨F1, rfl, hs1, hv⟩ := exec_bf hP n N F Ω k t s v hb.1 hs hr
      refine Stab.bind (sub u (by simp [Term.sz]; omega) hb.2 (fun h hh => by simp [Term.calls, hh]) F1 hs1)
        fun s w => ?_
      exact Stab.of_eq (fun _ => rfl) (by split <;> simp)
    | mtch p tz y ts =>
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at hb
      refine Stab.bind' (Stab.of_eq (fun _ => rfl) (access_ne_oof' _ _ _ _)) fun n s c hr => ?_
      obtain ⟨rfl, _⟩ := access_bf hs hr
      cases c with
      | zero => exact sub tz (by simp [Term.sz]; omega) hb.1 (fun h hh => by simp [Term.calls, hh]) F hs
      | succ _ =>
        exact sub _ (by simp [Term.sz, Term.sz_substVar]; omega) (by rw [Term.noBorrow_substVar]; exact hb.2)
          (fun h hh => by simp [Term.calls, Term.calls_substVar] at hh ⊢; simp [hh]) F hs
      | _ => exact Stab.of_eq (fun _ => rfl) (by first | simp | (split <;> simp))
    | call f args cc =>
      simp only [exec]
      cases hf : P.find f with
      | none => exact Stab.of_eq (fun _ => rfl) (by simp)
      | some d =>
        simp only
        by_cases hp : d.ret = .prop
        · simp only [hp, if_true]; exact Stab.of_eq (fun _ => rfl) (by simp)
        · simp only [hp, if_false]
          have hbl := Term.noBorrowList_iff.mp (by simpa [Term.noBorrow] using hb)
          have hargs : ∀ a ∈ args, ∀ F, BFSt N F Ω → ∃ n, exec P n ⟨F :: Ω, k⟩ a ≠ .oof := fun a ha F hs =>
            ih a (by have := Term.sz_lt_szList ha; simp [Term.sz] at hsz; omega) (hbl a ha)
              (fun h hh => hc h (by simp only [Term.calls, List.mem_cons, Term.mem_callsList];
                                    exact Or.inr ⟨a, ha, hh⟩)) N F Ω k hs
          refine Stab.bind' (execArgs_stab_bf hP args hbl hargs 0 F hs) fun n s _ hr => ?_
          obtain ⟨F1, rfl, hs1⟩ := execArgs_bf (exec_bf hP n) args 0 F _ _ hbl hs hr
          split
          · exact Stab.of_eq (fun _ => rfl) (by simp)
          · rename_i ws s' htt
            obtain ⟨F2, rfl, hs2, hws⟩ := takeTemps_bf _ F1 ws s' hs1 htt
            exact Stab.ofCallWith (hc f (by simp [Term.calls]) ws d hf cc N F2 Ω k hs2 hws)

theorem callTermBF_of_body {P : Prog} {h : String} {d : FunDef} (hd : P.find h = some d)
    (hb : ∀ b, d.body = some b → ∀ N F Ω k, BFSt N F Ω → ∃ n, exec P n ⟨F :: Ω, k⟩ b ≠ .oof)
    (ws : List Val) : CallTermBF P h ws := by
  intro d' hd' cc N F Ω k hs hws
  rw [hd] at hd'; cases hd'
  cases hbd : d.body with
  | none => exact ⟨0, callWith_ne_oof (fun b hb' => by simp [hbd] at hb')⟩
  | some b =>
    have hp := paramFrame_bf (N := N) d (d.params.map Prod.fst) ws hws
    obtain ⟨n, hn⟩ := hb b hbd N (paramFrame d ws) (F :: Ω) k ⟨hp.1, hs.env_nb, hp.2⟩
    exact ⟨n, callWith_ne_oof (fun b' hb' => by rw [hbd] at hb'; cases hb'; exact hn)⟩

/-- In an ordered borrow-free program, if every call to a recursive definition terminates from
borrow-free call points, every call does. -/
theorem termination_of_calls_bf {P : Prog} (hord : Guard.Ordered P) (hP : P.BF)
    (hrec : ∀ h d, P.find h = some d → d.recPos.isSome → ∀ ws, CallTermBF P h ws) :
    ∀ h ws, CallTermBF P h ws := by
  have key : ∀ n (A : Prog) f d B, A.length < n → P = A ++ (f, d) :: B → ∀ ws, CallTermBF P f ws := by
    intro n
    induction n with
    | zero => intro A f d B h; omega
    | succ n ih =>
      intro A f d B hlen hPe ws
      obtain ⟨_, hfA, hcalls⟩ := orderedAux_split A [] f d B (by rw [← hPe]; exact hord)
      have hd : P.find f = some d := by rw [hPe]; exact lookup_append_of_not_mem hfA
      cases hr : d.recPos with
      | some j => exact hrec f d hd (by simp [hr]) ws
      | none =>
        refine callTermBF_of_body hd (fun b hb N F Ω k hs =>
          exec_total_bf hP (b.sz + 1) b (by omega) ((hP f d hd).body b hb) (fun g hg ws' => ?_) N F Ω k hs) ws
        rcases hcalls b hb g hg with h1 | h1 | h1
        · simp at h1
        · obtain ⟨⟨g', dg⟩, hmem, rfl⟩ := List.mem_map.mp h1
          obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hmem
          exact ih A₁ g' dg (A₂ ++ (f, d) :: B) (by simp at hlen; omega) (by rw [hPe]; simp) ws'
        · simp [hr] at h1
  intro h ws d hd
  obtain ⟨A, B, hPe, _⟩ := List.lookup_eq_some_iff.mp hd
  exact key (A.length + 1) A h d B (by omega) hPe ws d hd

theorem termination_of_recCalls_bf {P : Prog} (hord : Guard.Ordered P) (hP : P.BF)
    (hrec : ∀ h d, P.find h = some d → d.recPos.isSome → ∀ ws, CallTermBF P h ws)
    (t : Term) (ht : t.noBorrow = true) {N : Nat} {F : Frame} {Ω : Env} {k : Nat} (hs : BFSt N F Ω) :
    ∃ n, exec P n ⟨F :: Ω, k⟩ t ≠ .oof :=
  exec_total_bf hP (t.sz + 1) t (by omega) ht (fun h _ ws => termination_of_calls_bf hord hP hrec h ws) N F Ω k hs

end OchrMeta
