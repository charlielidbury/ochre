import Ochr.Meaning.Steps.FrameJ2

/-!
# The frame property over `FrameRelS`, proved for the label-free fragment (model6, 2026-11-21; docs/31 D129)

`FrameProp.run_frame` (open) compares a body's run in place (the callee's frame pushed on the caller's
state) with its run in the closure's own state. Since D127/D128 the comparison is `FrameRelS`: every
binding of the callee's frame equal up to the renaming of labels, but the function's own binding (index
`i` of the top frame), which each side holds at its own type and is related by `SelfRel` only.

This file proves the property for a closed class of bodies with no borrow parameter (`ks = []`) and no
label anywhere in the frame: the LABEL-FREE fragment (`LFTy`: `Z`, `S(u)`, a read of a number variable,
`x := u` at a number variable, `let`, `;`; the fragment `FTy` without `&x` and `*y := u`). There:
- the run never reads the caller's frames, never makes a label, and never ends one (every [Access] at a
  position of the callee's frame reaches no label: the caller's borrows have no site there, `FrameStart`);
- every binding of the callee's frame but the function's own holds a future-free value with no label,
  so the two sides' top frames are EQUAL but at the function's binding (`TopLF`);
- the run does not read the tail flag or the hint (each clause runs its sub-terms at fixed ones);
- no whole-state strict test is reached (the places are whole variables: `lentOk` holds at `[]`), so the
  in-place state need not be good (`SGood` is not a hypothesis).

The relation the induction carries is `LF` (the two top frames as `TopLF`, the caller's frames and every
record of the in-place state as at the call, the closure's state with no holder and no site); `lf_start`
reads it off `FrameRelS` and `lf_end` gives `FrameRelS` back. `FrameJ2` is then an instance
(`frameJ2_holds`).
-/

namespace Ochr.Meaning.Steps.Form

open Ochr Ochr.Meaning Ochr.Meaning.Steps
open Classical

namespace FrameFrag

open FrameJ2

/-! ## Agreement of two runs, and the run's combinators -/

/-- Two optional results agree: both fail, or the same result, carrying no label, at states related by `P`. -/
def Agree (P : SState → SState → Prop) : Option (Res × SState) → Option (Res × SState) → Prop
  | none, none => True
  | some (r, t), some (r', t') => r = r' ∧ r.2.label = none ∧ P t t'
  | _, _ => False

theorem agree_none {P : SState → SState → Prop} : Agree P none none := trivial

theorem agree_some {P : SState → SState → Prop} {r : Res} {t t' : SState} (hl : r.2.label = none) (h : P t t') :
    Agree P (some (r, t)) (some (r, t')) := ⟨rfl, hl, h⟩

theorem agree_erasedIf {P : SState → SState → Prop} (fl : Bool × Bool) {x x' : SM Res} {s s' : SState}
    (hs : P s s') (h : Agree P (x s) (x' s')) : Agree P (SM.erasedIf fl x s) (SM.erasedIf fl x' s') := by
  unfold SM.erasedIf SM.stmtIf
  cases hx : x s with
  | none =>
    cases hx' : x' s' with
    | none => by_cases h2 : fl.2 <;> by_cases h1 : fl.1 <;> simp [h1, h2, Agree]
    | some y => rw [hx, hx'] at h; exact h.elim
  | some y =>
    cases hx' : x' s' with
    | none => rw [hx, hx'] at h; exact h.elim
    | some y' =>
      rw [hx, hx'] at h
      obtain ⟨⟨v, T⟩, t⟩ := y
      obtain ⟨⟨v', T'⟩, t'⟩ := y'
      obtain ⟨e, hl, hP⟩ := h
      cases e
      split
      · cases v <;> first | exact agree_some rfl hs | trivial
      · split
        · exact agree_some rfl hs
        · exact agree_some hl hP

theorem agree_strictS {P : SState → SState → Prop} (R : DataRead) {x x' : SM Res} {s s' : SState}
    (h : Agree P (x s) (x' s')) : Agree P (SM.strictS R x s) (SM.strictS R x' s') := by
  unfold SM.strictS
  cases hx : x s with
  | none =>
    cases hx' : x' s' with
    | none => trivial
    | some y => rw [hx, hx'] at h; exact h.elim
  | some y =>
    cases hx' : x' s' with
    | none => rw [hx, hx'] at h; exact h.elim
    | some y' =>
      rw [hx, hx'] at h
      obtain ⟨r, t⟩ := y
      obtain ⟨r', t'⟩ := y'
      obtain ⟨e, hl, hP⟩ := h
      cases e
      dsimp only
      split
      · exact agree_some hl hP
      · trivial

theorem agree_guarded {P : SState → SState → Prop} {ok ok' : SState → Prop} {x x' : SM Res} {s s' : SState}
    (hok : ok s ↔ ok' s') (h : Agree P (x s) (x' s')) : Agree P (SM.guarded ok x s) (SM.guarded ok' x' s') := by
  unfold SM.guarded
  by_cases ho : ok s
  · rw [if_pos ho, if_pos (hok.1 ho)]; exact h
  · rw [if_neg ho, if_neg (fun h' => ho (hok.2 h'))]; trivial

/-- A bind on two agreeing runs, its continuations agreeing at agreeing inputs. -/
theorem agree_bind {P Q : SState → SState → Prop} {o o' : Option (Res × SState)} (h : Agree P o o')
    (f f' : Res × SState → Option (Res × SState))
    (hf : ∀ r t t', r.2.label = none → P t t' → Agree Q (f (r, t)) (f' (r, t'))) :
    Agree Q (o.bind f) (o'.bind f') := by
  cases o with
  | none => cases o' with
    | none => trivial
    | some _ => exact h.elim
  | some y => cases o' with
    | none => exact h.elim
    | some y' =>
      obtain ⟨r, t⟩ := y
      obtain ⟨r', t'⟩ := y'
      obtain ⟨e, hl, hP⟩ := h
      cases e
      exact hf r t t' hl hP


/-- A bind of the run's monad on two agreeing runs, its continuations agreeing at agreeing inputs. -/
theorem agree_smBind {P Q : SState → SState → Prop} {x x' : SM Res} {f f' : Res → SM Res} {s s' : SState}
    (h : Agree P (x s) (x' s')) (hf : ∀ r t t', r.2.label = none → P t t' → Agree Q (f r t) (f' r t')) :
    Agree Q ((x >>= f) s) ((x' >>= f') s') := by
  simp only [Bind.bind, Monad.toBind, instMonadSM]
  cases hx : x s with
  | none =>
    cases hx' : x' s' with
    | none => trivial
    | some y => rw [hx, hx'] at h; exact h.elim
  | some y =>
    cases hx' : x' s' with
    | none => rw [hx, hx'] at h; exact h.elim
    | some y' =>
      rw [hx, hx'] at h
      obtain ⟨r, t⟩ := y
      obtain ⟨r', t'⟩ := y'
      obtain ⟨e, hl, hP⟩ := h
      cases e
      exact hf r t t' hl hP


/-! ## The label-free relation -/

/-- A binding holding a future-free value under a type with no label. -/
def Plain (b : SBinding) : Prop := b.ty.label = none ∧ ∀ ψ ψ' : Future, b.val ψ = b.val ψ'

/-- The two top frames: equal but at the function's own binding `i` (in place `bS`, in the closure
`bS'`), every other binding plain, the temporaries the same and future-free. -/
structure TopLF (i : Nat) (bS bS' : SBinding) (F F' : SFrame) : Prop where
  len : F.binds.length = F'.binds.length
  self : F.binds[i]? = some bS
  self' : F'.binds[i]? = some bS'
  eq : ∀ j, j ≠ i → F.binds[j]? = F'.binds[j]?
  plain : ∀ j b, j ≠ i → F.binds[j]? = some b → Plain b
  temps : F.temps = F'.temps
  tplain : ∀ v ∈ F.temps, ∀ ψ ψ' : Future, v ψ = v ψ'

/-- The records the label-free run never changes: the in-place state's holders, sites, records and
counter are those of the state `S` at the call, none of its holders or sites in the callee's frame
(index `L.length`); the closure's state has no holder and no site, its counter that of `S'`. -/
structure Recs (L : List SFrame) (S S' s s' : SState) : Prop where
  shape : s.shape = S.shape
  lent : s.lent = S.lent
  next : s.nextLoan = S.nextLoan
  hm : s.heldMem = S.heldMem
  ht : s.heldTy = S.heldTy
  topShape : ∀ p : Pos, p.frameOf = L.length → S.shape p = none
  topLent : ∀ l (x : Site), x ∈ S.lent l → x.pos.frameOf ≠ L.length
  shape' : ∀ p, s'.shape p = none
  lent' : ∀ l, s'.lent l = []
  next' : s'.nextLoan = S'.nextLoan

/-- **The label-free frame relation**: in place the caller's frames `L` and the callee's frame `F` on
top, with `i + 1 + n` bindings (the function's own at `i`, `n` after it); the closure two frames, its
top `F'`; the top frames related by `TopLF`; the records as at the call (`Recs`). -/
def LF (i : Nat) (bS bS' : SBinding) (L : List SFrame) (S S' : SState) (n : Nat) (s s' : SState) : Prop :=
  ∃ F F' C, s.env = L ++ [F] ∧ s'.env = [C, F'] ∧ TopLF i bS bS' F F' ∧ F.binds.length = i + 1 + n ∧
    Recs L S S' s s'

theorem topIdx_of_env {s : SState} {L : List SFrame} {F : SFrame} (h : s.env = L ++ [F]) : s.topIdx = L.length := by
  simp [SState.topIdx, h]

theorem topIdx_of_env' {s : SState} {C F : SFrame} (h : s.env = [C, F]) : s.topIdx = 1 := by
  simp [SState.topIdx, h]

theorem modify_two {α : Type _} (C F : α) (g : α → α) : [C, F].modify 1 g = [C, g F] := by simp [List.modify]

/-- The top frames stay related when the same position `k ≠ i` is rewritten, to a future-free value. -/
theorem topLF_modify {i k : Nat} {bS bS' : SBinding} {F F' : SFrame} (h : TopLF i bS bS' F F') (hk : k ≠ i)
    (w : SVal) (hw : ∀ ψ ψ' : Future, w ψ = w ψ') :
    TopLF i bS bS' { F with binds := F.binds.modify k fun b => { b with val := w } }
      { F' with binds := F'.binds.modify k fun b => { b with val := w } } := by
  refine ⟨by simp [h.len], ?_, ?_, fun j hj => ?_, fun j b hj hb => ?_, h.temps, h.tplain⟩
  · simp only [List.getElem?_modify, if_neg hk, h.self]; rfl
  · simp only [List.getElem?_modify, if_neg hk, h.self']; rfl
  · simp only [List.getElem?_modify, h.eq j hj]
  · simp only [List.getElem?_modify] at hb
    cases hx : F.binds[j]? with
    | none => rw [hx] at hb; cases hb
    | some x =>
      rw [hx] at hb
      by_cases e : k = j
      · subst e
        simp only [if_true, Option.map_eq_map, Option.map_some, Option.some.injEq] at hb
        subst hb
        exact ⟨(h.plain k x hj hx).1, hw⟩
      · simp only [e, if_false, Option.map_eq_map, Option.map_some, Option.some.injEq] at hb
        subst hb
        exact h.plain j x hj hx

/-- The top frames stay related when the same plain binding is pushed. -/
theorem topLF_push {i : Nat} {bS bS' : SBinding} {F F' : SFrame} (h : TopLF i bS bS' F F') (hi : i < F.binds.length)
    (b : SBinding) (hb : Plain b) :
    TopLF i bS bS' { F with binds := F.binds ++ [b] } { F' with binds := F'.binds ++ [b] } := by
  have hi' : i < F'.binds.length := h.len ▸ hi
  refine ⟨by simp [h.len], ?_, ?_, fun j hj => ?_, fun j c hj hc => ?_, h.temps, h.tplain⟩
  · rw [List.getElem?_append_left hi]; exact h.self
  · rw [List.getElem?_append_left hi']; exact h.self'
  · by_cases hl : j < F.binds.length
    · rw [List.getElem?_append_left hl, List.getElem?_append_left (h.len ▸ hl)]; exact h.eq j hj
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by rw [← h.len]; omega), h.len]
  · by_cases hl : j < F.binds.length
    · rw [List.getElem?_append_left hl] at hc; exact h.plain j c hj hc
    · rw [List.getElem?_append_right (by omega)] at hc
      cases e : j - F.binds.length with
      | zero => rw [e] at hc; simp only [List.getElem?_cons_zero, Option.some.injEq] at hc; subst hc; exact hb
      | succ m => rw [e] at hc; simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hc

/-- The top frames stay related when their last binding, not the function's own, is dropped. -/
theorem topLF_drop {i : Nat} {bS bS' : SBinding} {F F' : SFrame} (h : TopLF i bS bS' F F')
    (hi : i + 1 < F.binds.length) :
    TopLF i bS bS' { F with binds := F.binds.dropLast } { F' with binds := F'.binds.dropLast } := by
  refine ⟨by simp [h.len], ?_, ?_, fun j hj => ?_, fun j c hj hc => ?_, h.temps, h.tplain⟩
  · rw [List.getElem?_dropLast, if_pos (by omega)]; exact h.self
  · rw [List.getElem?_dropLast, if_pos (by rw [← h.len]; omega)]; exact h.self'
  · rw [List.getElem?_dropLast, List.getElem?_dropLast, h.len, h.eq j hj]
  · rw [List.getElem?_dropLast] at hc
    split at hc
    · exact h.plain j c hj hc
    · cases hc

/-! ## The state operations of the label-free run keep `LF` -/

section
variable {i : Nat} {bS bS' : SBinding} {L : List SFrame} {S S' : SState}

/-- Dropping the last binding of the top frame keeps the holders where the top frame holds none. -/
theorem dropLast_shape {s : SState} (h : ∀ p : Pos, p.frameOf = s.topIdx → s.shape p = none) :
    s.dropLast.shape = s.shape := by
  funext p
  simp only [SState.dropLast]
  cases hl : s.env.getLast? with
  | none => simp
  | some fr =>
    dsimp only
    split
    · rename_i e
      simp only [Option.some.injEq] at e
      subst e
      exact (h _ rfl).symm
    · rfl

/-- A write of the same future-free value at the same position of the two top frames, not the
function's own binding. -/
theorem lf_setAt {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {k : Nat} (hk : k ≠ i) (w : SVal)
    (hw : ∀ ψ ψ' : Future, w ψ = w ψ') :
    LF i bS bS' L S S' n (s.setAt (.bind L.length k) w) (s'.setAt (.bind 1 k) w) := by
  obtain ⟨F, F', C, he, he', ht, hl, hr⟩ := h
  refine ⟨_, _, C, ?_, ?_, topLF_modify ht hk w hw, by simpa using hl, ?_⟩
  · simp only [SState.setAt, he, modify_append_len]
  · simp only [SState.setAt, he', modify_two]
  · exact ⟨hr.shape, hr.lent, hr.next, hr.hm, hr.ht, hr.topShape, hr.topLent, hr.shape', hr.lent', hr.next'⟩

/-- A push of the same plain binding on the two top frames. -/
theorem lf_pushBind {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') (b : SBinding) (hb : Plain b) :
    LF i bS bS' L S S' (n + 1) (s.pushBind b) (s'.pushBind b) := by
  obtain ⟨F, F', C, he, he', ht, hl, hr⟩ := h
  refine ⟨_, _, C, ?_, ?_, topLF_push ht (by omega) b hb, by simp [hl] <;> omega, ?_⟩
  · simp only [SState.pushBind, topIdx_of_env he, he, modify_append_len]
  · simp only [SState.pushBind, topIdx_of_env' he', he', modify_two]
  · exact ⟨hr.shape, hr.lent, hr.next, hr.hm, hr.ht, hr.topShape, hr.topLent, hr.shape', hr.lent', hr.next'⟩

/-- The drop of the last binding of the two top frames (a `let`'s). -/
theorem lf_dropLast {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' (n + 1) s s') :
    LF i bS bS' L S S' n s.dropLast s'.dropLast := by
  obtain ⟨F, F', C, he, he', ht, hl, hr⟩ := h
  refine ⟨_, _, C, ?_, ?_, topLF_drop ht (by omega), by simp [hl] <;> omega, ?_⟩
  · simp only [SState.dropLast, topIdx_of_env he, he, modify_append_len]
  · simp only [SState.dropLast, topIdx_of_env' he', he', modify_two]
  · refine ⟨?_, hr.lent, hr.next, hr.hm, hr.ht, hr.topShape, hr.topLent, ?_, hr.lent', hr.next'⟩
    · rw [dropLast_shape (fun p hp => by rw [hr.shape]; exact hr.topShape p (by rw [hp, topIdx_of_env he])), hr.shape]
    · rw [dropLast_shape (fun p _ => hr.shape' p)]; exact hr.shape'

/-- The two scopes agree (the function's own binding read alike on both sides). -/
theorem lf_scope {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') (hd : bS.decl = bS'.decl) :
    scopeOf s = scopeOf s' := by
  obtain ⟨F, F', C, he, he', ht, -, -⟩ := h
  simp only [scopeOf, he, he', List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.getLast?_cons_cons]
  congr 1
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map]
  by_cases hj : j = i
  · subst hj; rw [ht.self, ht.self']; simp [hd]
  · rw [ht.eq j hj]

end

/-! ## What the label-free run reads -/

/-- [Access] at a position no live label is lent at changes nothing. -/
theorem access_self {s : SState} {p : Pos} {hit : List Step → Bool} (h : ∀ l, s.reached p hit l = false) :
    s.access p hit = s := by
  have hstep : (s.liveLabels.filter (s.reached p hit)).foldl SState.endLabel s = s := by
    rw [List.filter_eq_nil_iff.2 (fun l _ => by simp [h l])]; rfl
  unfold SState.access
  dsimp only
  generalize List.range s.liveLabels.length = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, hstep, ih]

/-- Its ends (none) are strict-OK. -/
theorem accessOk_self (K : RunCtx) (φ : Future) {s : SState} {p : Pos} {hit : List Step → Bool}
    (h : ∀ l, s.reached p hit l = false) : AccessOk K φ s p hit := by
  have hround : accRound p hit s = s := by
    unfold accRound
    rw [List.filter_eq_nil_iff.2 (fun l _ => by simp [h l])]; rfl
  have hk : ∀ k, (List.range k).foldl (fun t _ => accRound p hit t) s = s := by
    intro k
    generalize List.range k = xs
    induction xs with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons, hround, ih]
  intro k _
  rw [hk k, List.filter_eq_nil_iff.2 (fun l _ => by simp [h l])]
  trivial

/-- A write at a whole place: its definedness test always passes. -/
theorem setContent_nil (K : RunCtx) (φ : Future) (pos : Pos) (v : Sem) (s : SState) :
    setContent K φ pos [] v s = some (⟨⟩, s.setAt pos fun _ => v) := by
  unfold setContent
  rw [if_pos (fun _ _ => by rw [Sem.updAt.eq_def]; rfl)]
  congr 2

section
variable {i : Nat} {bS bS' : SBinding} {L : List SFrame} {S S' : SState}

/-- A variable after the function's own binding: the same position on both sides (frame `L.length` in
place, frame 1 in the closure), holding the same plain binding. -/
theorem lf_var {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {j : Nat} (hj : j < n) :
    ∃ b, Plain b ∧ s.varPos j = some (.bind L.length (i + n - j)) ∧ s'.varPos j = some (.bind 1 (i + n - j)) ∧
      s.valAt (.bind L.length (i + n - j)) = b.val ∧ s'.valAt (.bind 1 (i + n - j)) = b.val ∧
      s.tyAt (.bind L.length (i + n - j)) = b.ty ∧ s'.tyAt (.bind 1 (i + n - j)) = b.ty := by
  obtain ⟨F, F', C, he, he', ht, hl, -⟩ := h
  have hk : i + n - j ≠ i := by omega
  have hlt : i + n - j < F.binds.length := by omega
  obtain ⟨b, hb⟩ : ∃ b, F.binds[i + n - j]? = some b := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hb' : F'.binds[i + n - j]? = some b := by rw [← ht.eq _ hk, hb]
  have hF : s.env[L.length]? = some F := by simp [he]
  have hF' : s'.env[1]? = some F' := by simp [he']
  refine ⟨b, ht.plain _ b hk hb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [SState.varPos, he, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      topIdx_of_env he]
    rw [if_pos (by omega)]; congr 3; omega
  · simp only [SState.varPos, he', List.getLast?_cons_cons, List.getLast?_singleton, topIdx_of_env' he']
    rw [if_pos (by rw [← ht.len]; omega)]; congr 3; rw [← ht.len]; omega
  · simp [SState.valAt, hF, hb]
  · simp [SState.valAt, hF', hb']
  · simp [SState.tyAt, hF, hb]
  · simp [SState.tyAt, hF', hb']

/-- No live label is lent at a position of the in-place callee's frame, nor anywhere in the closure. -/
theorem lf_noReach {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') (k : Nat) (hit : List Step → Bool) :
    (∀ l, s.reached (.bind L.length k) hit l = false) ∧ (∀ l, s'.reached (.bind 1 k) hit l = false) := by
  obtain ⟨-, -, -, -, -, -, -, hr⟩ := h
  refine ⟨fun l => ?_, fun l => ?_⟩
  · simp only [SState.reached, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro x hx e
    exact absurd (by rw [e]; rfl) (hr.topLent l x (hr.lent ▸ hx))
  · simp [SState.reached, hr.lent' l]

end

section
variable (K : RunCtx) (φ : Future) {i : Nat} {bS bS' : SBinding} {L : List SFrame} {S S' : SState}

/-- The content of a variable after the function's own binding: the same on both sides, the state as it was. -/
theorem lf_contentOf {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {j : Nat} (hj : j < n) :
    ∃ b, Plain b ∧ contentOf K φ (.var j) s = some ((b.val φ, b.ty, .bind L.length (i + n - j), []), s) ∧
      contentOf K φ (.var j) s' = some ((b.val φ, b.ty, .bind 1 (i + n - j), []), s') := by
  obtain ⟨b, hb, hv, hv', hva, hva', hty, hty'⟩ := lf_var h hj
  obtain ⟨hn, hn'⟩ := lf_noReach h (i + n - j) (dataHit [])
  refine ⟨b, hb, ?_, ?_⟩
  · simp only [contentOf, resolve, Place.steps, hv, Option.map_some, access_self hn, hva, hty, Sem.follow,
      List.isEmpty_nil, if_true]
    rw [hb.2 _ φ]
  · simp only [contentOf, resolve, Place.steps, hv', Option.map_some, access_self hn', hva', hty', Sem.follow,
      List.isEmpty_nil, if_true]
    rw [hb.2 _ φ]

theorem lf_contentOk {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {j : Nat} (hj : j < n) :
    ContentOk K φ (.var j) s ∧ ContentOk K φ (.var j) s' := by
  obtain ⟨b, -, hv, hv', -⟩ := lf_var h hj
  obtain ⟨hn, hn'⟩ := lf_noReach h (i + n - j) (dataHit [])
  simp only [ContentOk, resolve, Place.steps, hv, hv', Option.map_some]
  exact ⟨accessOk_self K φ hn, accessOk_self K φ hn'⟩

/-- **[Read] of a variable**: the same result, carrying no label, and related states (a move writes `⊥`
at the same position of both top frames). -/
theorem lf_readPlace {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {j : Nat} (hj : j < n)
    (cp : Bool) :
    Agree (LF i bS bS' L S S' n) (readPlace K φ (.var j) cp s) (readPlace K φ (.var j) cp s') := by
  obtain ⟨b, hb, hc, hc'⟩ := lf_contentOf K φ h hj
  have hsh : s.shape (.bind L.length (i + n - j)) = none := by
    obtain ⟨-, -, -, -, -, -, -, hr⟩ := h
    rw [hr.shape]; exact hr.topShape _ rfl
  have hsh' : s'.shape (.bind 1 (i + n - j)) = none := by
    obtain ⟨-, -, -, -, -, -, -, hr⟩ := h
    exact hr.shape' _
  unfold readPlace
  rw [hc, hc']
  simp only [Bind.bind, Option.bind, setContent_nil, hsh, hsh', List.isEmpty_nil, if_true]
  by_cases hw : (b.val φ).whole
  · by_cases hr : ReadGood K.dm.read b.ty.m (b.val φ)
    · cases cp
      · simp only [hw, hr, not_true, if_false, Bool.false_eq_true]
        refine agree_some rfl (lf_setAt h (by omega) _ (fun _ _ => rfl))
      · simp only [hw, hr, not_true, if_false, if_true]
        exact agree_some rfl h
    · simp only [hw, hr, not_true, not_false_eq_true, if_false, if_true]; trivial
  · simp only [hw, not_false_eq_true, if_true]; trivial

theorem lentOk_var (j : Nat) (s : SState) : lentOk K φ (.var j) s := by
  unfold lentOk resolve
  cases hv : s.varPos j <;> simp [Place.steps, hv]

/-- The type of a variable after the function's own binding, read alike. -/
theorem lf_placeTy {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {j : Nat} (hj : j < n) :
    placeTy K φ (.var j) s = placeTy K φ (.var j) s' := by
  obtain ⟨b, -, hc, hc'⟩ := lf_contentOf K φ h hj
  simp only [placeTy, hc, hc']

/-- **[Assign]'s write at a variable**: the strict end tests pass alike (nothing is lent there), the
same value written at the same position of both top frames. -/
theorem lf_assignAt {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') {j : Nat} (hj : j < n) (v : Sem) :
    (AssignOk K φ (.var j) s ↔ AssignOk K φ (.var j) s') ∧
    Agree (LF i bS bS' L S S' n) (assignAt K φ (.var j) v none s) (assignAt K φ (.var j) v none s') := by
  obtain ⟨b, -, hv, hv', -⟩ := lf_var h hj
  obtain ⟨hn, hn'⟩ := lf_noReach h (i + n - j) (dataHit [])
  have hsh : s.shape (.bind L.length (i + n - j)) = none := by
    obtain ⟨-, -, -, -, -, -, -, hr⟩ := h
    rw [hr.shape]; exact hr.topShape _ rfl
  have hsh' : s'.shape (.bind 1 (i + n - j)) = none := by
    obtain ⟨-, -, -, -, -, -, -, hr⟩ := h
    exact hr.shape' _
  refine ⟨?_, ?_⟩
  · simp only [AssignOk, resolve, Place.steps, hv, hv', Option.map_some, List.isEmpty_nil, hsh, hsh',
      Option.isSome_none, Bool.and_false, access_self hn, access_self hn']
    exact ⟨fun _ => ⟨fun _ => accessOk_self K φ hn', fun _ _ e => by simp [hsh'] at e⟩,
      fun _ => ⟨fun _ => accessOk_self K φ hn, fun _ _ e => by simp [hsh] at e⟩⟩
  · simp only [assignAt, resolve, Place.steps, hv, hv', Option.map_some, List.isEmpty_nil, hsh, hsh',
      Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false, if_true, access_self hn, access_self hn',
      setContent_nil]
    exact agree_some rfl (lf_setAt h (by omega) _ (fun _ _ => rfl))

/-- The end of a `let` in the label-free run: its binding holds no borrow and nothing is lent at it, so
the drop's test passes and its [Access] changes nothing, on both sides. -/
theorem lf_letEnd {n : Nat} {s s' : SState} (h : LF i bS bS' L S S' n s s') :
    (∃ F, s.env.getLast? = some F ∧ s.shape (.bind s.topIdx (F.binds.length - 1)) = none) ∧
    (∃ F', s'.env.getLast? = some F' ∧ s'.shape (.bind s'.topIdx (F'.binds.length - 1)) = none) ∧
    LetLendersOk K φ s ∧ LetLendersOk K φ s' ∧ letLenders s = s ∧ letLenders s' = s' := by
  have hn := lf_noReach h
  obtain ⟨F, F', C, he, he', -, -, hr⟩ := h
  have hl : s.env.getLast? = some F := by simp [he]
  have hl' : s'.env.getLast? = some F' := by simp [he']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨F, hl, by rw [hr.shape, topIdx_of_env he]; exact hr.topShape _ rfl⟩
  · exact ⟨F', hl', hr.shape' _⟩
  · unfold LetLendersOk; rw [hl, topIdx_of_env he]; exact accessOk_self K φ (hn _ _).1
  · unfold LetLendersOk; rw [hl', topIdx_of_env' he']; exact accessOk_self K φ (hn _ _).2
  · unfold letLenders; rw [hl, topIdx_of_env he]; exact access_self (hn _ _).1
  · unfold letLenders; rw [hl', topIdx_of_env' he']; exact access_self (hn _ _).2

end

/-! ## The label-free fragment, and the frame property on it -/

/-- **The label-free fragment** over `n` variables of the callee's frame (after the function's own
binding): `Z`, `S(u)`, a read of a variable, `x := u` at a variable (only where `a`), `let x = u; w` (its
tail over one more), `u; w`. Every fragment term (`FTy`) with no `&` and no borrow-typed variable is one. -/
inductive LFree (a : Bool) : Nat → Term → Prop
  | zero (n : Nat) : LFree a n .zero
  | succ (n : Nat) (u : Term) : LFree a n u → LFree a n (.succ u)
  | var (n j : Nat) : j < n → LFree a n (.place (.var j))
  | asg (n j : Nat) (u : Term) : a = true → j < n → LFree a n u → LFree a n (.assign (.var j) u)
  | letIn (n : Nat) (x : Hint) (u w : Term) : LFree a n u → LFree a (n + 1) w → LFree a n (.letIn x u w)
  | seq (n : Nat) (u w : Term) : LFree a n u → LFree a n w → LFree a n (.seq u w)

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future) {i : Nat} {bS bS' : SBinding} {L : List SFrame} {S S' : SState}

/-- **The frame property on the label-free fragment, with the function's own binding exempt**: from
`LF`-related states a label-free term runs, at ANY tail flags and hints on the two sides, to the same
result, carrying no label, and `LF`-related states, or fails on both. Hypotheses: the decision table
invalidates nothing (`noInv`, the fuel-free table's by definition) and the two sides read the
function's own binding alike (`SelfRel`'s reading clause). -/
theorem lf_run {a : Bool} (hNI : a = true → ∀ sc p, K.D.invalidated sc p = []) (hd : bS.decl = bS'.decl) :
    ∀ n t, LFree a n t → ∀ (s s' : SState) (tl tl' : Bool) (h h' : TyS), LF i bS bS' L S S' n s s' →
      Agree (LF i bS bS' L S S' n) (runT K ρ φ tl h t s) (runT K ρ φ tl' h' t s') := by
  intro n t ht
  induction ht with
  | zero n =>
    intro s s' tl tl' h h' hr
    rw [runT, runT]
    exact agree_some rfl hr
  | succ n u hu ih =>
    intro s s' tl tl' h h' hr
    rw [runT, runT]
    show Agree _ (SM.erasedIf (K.D.flags (scopeOf s) _) _ s) (SM.erasedIf (K.D.flags (scopeOf s') _) _ s')
    rw [← lf_scope hr hd]
    refine agree_erasedIf _ hr (agree_strictS _ (agree_smBind (ih s s' false false _ _ hr) ?_))
    intro r t t' _ ht
    exact agree_some rfl ht
  | var n j hj =>
    intro s s' tl tl' h h' hr
    rw [runT, runT]
    show Agree _ (SM.erasedIf (K.D.flags (scopeOf s) _) (SM.guarded _ (readPlace K φ _
        (K.D.copy (K.D.placeDecl (scopeOf s) _)))) s)
      (SM.erasedIf (K.D.flags (scopeOf s') _) (SM.guarded _ (readPlace K φ _
        (K.D.copy (K.D.placeDecl (scopeOf s') _)))) s')
    rw [← lf_scope hr hd]
    obtain ⟨hc, hc'⟩ := lf_contentOk K φ hr hj
    exact agree_erasedIf _ hr (agree_guarded (iff_of_true hc hc') (lf_readPlace K φ hr hj _))
  | asg n j u ha hj hu ih =>
    have hNI := hNI ha
    intro s s' tl tl' h h' hr
    rw [runT, runT]
    show Agree _ (SM.erasedIf (K.D.flags (scopeOf s) _) _ s) (SM.erasedIf (K.D.flags (scopeOf s') _) _ s')
    rw [← lf_scope hr hd]
    refine agree_erasedIf _ hr ?_
    dsimp only
    refine agree_bind (ih s s' false false _ _ hr) _ _ ?_
    rintro ⟨v, R⟩ t t' hl ht
    dsimp only at hl ⊢
    rw [lf_placeTy K φ ht hj]
    have hc : ∀ X : TyS, (v ∈ₛ[K.dm.read] X.m ∧ labTyOk t R.label X.m) ↔ (v ∈ₛ[K.dm.read] X.m ∧ labTyOk t' R.label X.m) :=
      fun X => by simp [labTyOk, hl]
    by_cases hcond : v ∈ₛ[K.dm.read] (placeTy K φ (.var j) t').m ∧ labTyOk t R.label (placeTy K φ (.var j) t').m
    · rw [if_pos hcond, if_pos ((hc _).1 hcond), hl]
      obtain ⟨hA, hag⟩ := lf_assignAt K φ ht hj v
      unfold SM.guarded
      by_cases hok : AssignOk K φ (.var j) t
      · rw [if_pos hok, if_pos (hA.1 hok)]
        cases ha : assignAt K φ (.var j) v none t with
        | none =>
          cases ha' : assignAt K φ (.var j) v none t' with
          | none => trivial
          | some y => rw [ha, ha'] at hag; exact hag.elim
        | some y =>
          cases ha' : assignAt K φ (.var j) v none t' with
          | none => rw [ha, ha'] at hag; exact hag.elim
          | some y' =>
            rw [ha, ha'] at hag
            obtain ⟨r, t₁⟩ := y
            obtain ⟨r', t₁'⟩ := y'
            obtain ⟨e, hl₁, h₁⟩ := hag
            cases e
            have hinv : ∀ x, invalidate K φ (.var j) x = x := fun x => by simp only [invalidate, hNI, List.foldl_nil]
            have hIO : ∀ x, InvalidateOk K φ (.var j) x := fun x => by unfold InvalidateOk; rw [hNI]; trivial
            dsimp only
            rw [hinv, hinv, if_pos ⟨hIO _, lentOk_var K φ j _⟩, if_pos ⟨hIO _, lentOk_var K φ j _⟩]
            exact agree_some hl₁ h₁
      · rw [if_neg hok, if_neg (fun h' => hok (hA.2 h'))]; trivial
    · rw [if_neg hcond, if_neg (fun h' => hcond ((hc _).2 h'))]; trivial
  | letIn n x u w hu hw ihu ihw =>
    intro s s' tl tl' h h' hr
    rw [runT, runT]
    show Agree _ (SM.erasedIf (K.D.flags (scopeOf s) _) _ s) (SM.erasedIf (K.D.flags (scopeOf s') _) _ s')
    rw [← lf_scope hr hd]
    refine agree_erasedIf _ hr ?_
    dsimp only
    rw [← lf_scope hr hd]
    refine agree_bind (ihu s s' false false _ _ hr) _ _ ?_
    rintro ⟨v, T⟩ t t' hl ht
    dsimp only at hl ⊢
    have hpush : ∀ y, pushBindShaped y { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } =
        y.pushBind { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } := fun y => by
      simp [pushBindShaped, hl]
    rw [hpush, hpush]
    have ht1 := lf_pushBind ht { ty := T, val := fun _ => v, decl := K.D.declOf (scopeOf s) u } ⟨hl, fun _ _ => rfl⟩
    refine agree_bind (ihw _ _ tl tl' _ _ ht1) _ _ ?_
    rintro ⟨r, R⟩ t₂ t₂' hl₂ ht₂
    dsimp only at hl₂ ⊢
    obtain ⟨⟨F₂, hF₂, e₁⟩, ⟨F₂', hF₂', e₂⟩, hk₁, hk₂, hd₁, hd₂⟩ := lf_letEnd K φ ht₂
    rw [hF₂, hF₂']
    dsimp only
    simp only [e₁, e₂, hk₁, hk₂, if_true, hd₁, hd₂]
    exact agree_some hl₂ (lf_dropLast ht₂)
  | seq n u w hu hw ihu ihw =>
    intro s s' tl tl' h h' hr
    rw [runT, runT]
    show Agree _ (SM.erasedIf (K.D.flags (scopeOf s) _) _ s) (SM.erasedIf (K.D.flags (scopeOf s') _) _ s')
    rw [← lf_scope hr hd]
    refine agree_erasedIf _ hr (agree_smBind (ihu s s' false false _ _ hr) ?_)
    intro r t t' hl ht
    have hD : ∀ y, DiscardOk K φ r.2 y := fun y => by simp [DiscardOk, hl]
    have hE : ∀ y, discardEnd r.2 y = y := fun y => by simp [discardEnd, hl]
    simp only [Bind.bind, Monad.toBind, instMonadSM, SM.guardMod_of (hD _), hE]
    exact ihw t t' tl tl' _ _ ht

end

/-! ## From `FrameRelS` to `LF` and back -/

/-- A binding related to a plain one by the renaming is that binding. -/
theorem bindRen_plain {σ : Nat → Nat} {x y : SBinding} (h : BindRen σ x y) (hy : Plain y) : x = y := by
  obtain ⟨hty, hd, hr, hv⟩ := h
  obtain ⟨hl, hc⟩ := hy
  have hv' : x.val = y.val := funext fun ψ => (hv ψ).trans (hc _ _)
  cases x with
  | mk xt xv xd xr =>
    cases y with
    | mk yt yv yd yr =>
      cases yt with
      | mk ym yl =>
        simp only at hl hty hd hr hv'
        subst hl hd hr hv'
        simp only [Option.map_none] at hty
        rw [hty]

/-- A plain binding is related to itself by every renaming. -/
theorem bindRen_of_plain (σ : Nat → Nat) {x : SBinding} (hx : Plain x) : BindRen σ x x := by
  refine ⟨?_, rfl, rfl, fun ψ => hx.2 _ _⟩
  cases x with
  | mk ty v d rb =>
    cases ty with
    | mk m lab =>
      obtain ⟨hl, -⟩ := hx
      simp only at hl
      subst hl
      rfl

theorem setTopBind_env' {s : SState} {C F : SFrame} (h : s.env = [C, F]) (i : Nat) (b : SBinding) :
    (setTopBind s i b).env = [C, { F with binds := F.binds.set i b }] := by
  simp [setTopBind, h, topIdx_of_env' h, modify_two]

theorem valAt_congr_frame {s t : SState} {p : Pos} (h : s.env[p.frameOf]? = t.env[p.frameOf]?) : s.valAt p = t.valAt p := by
  cases p with
  | bind f k => simp only [Pos.frameOf] at h; simp only [SState.valAt, h]
  | temp f k => simp only [Pos.frameOf] at h; simp only [SState.valAt, h]

theorem not_live_of_shape {s : SState} (h : ∀ p, s.shape p = none) (l : Nat) : ¬ s.Live l := by
  rw [SState.live_iff]; rintro ⟨p, -, hp⟩; rw [h p] at hp; cases hp

section
variable {R : DataRead} {σ : Nat → Nat} {s₀ : SState} {i : Nat}

/-- **`LF` read off `FrameRelS`** (no parameter label): where the closure's state holds no borrow and
lends nothing, and its top frame's bindings but the function's own, and its temporaries, are
future-free with no label. -/
theorem lf_start {S S' : SState} {C F' : SFrame} {n : Nat} (hrel : FrameRelS R σ s₀ [] i S S')
    (he' : S'.env = [C, F']) (hsh' : ∀ p, S'.shape p = none) (hlt' : ∀ l, S'.lent l = [])
    (hpl : ∀ j b, j ≠ i → F'.binds[j]? = some b → Plain b) (htp : ∀ v ∈ F'.temps, ∀ ψ ψ' : Future, v ψ = v ψ')
    (hn : F'.binds.length = i + 1 + n) :
    ∃ bS bS', topBind? S i = some bS ∧ topBind? S' i = some bS' ∧ SelfRel R bS bS' ∧
      BindRen σ bS bS ∧ ∃ L, S.env.length = L.length + 1 ∧ s₀.topIdx = L.length ∧ LF i bS bS' L S S' n S S' := by
  obtain ⟨b, b', hb, hb', hself, hFR⟩ := hrel
  obtain ⟨F, F'', hF, hF'', hlen, hbr, htl, htv⟩ := hFR.top
  have he'' := setTopBind_env' he' i b
  have hF''e : F'' = { F' with binds := F'.binds.set i b } := by
    rw [he''] at hF''; simp at hF''; exact hF''.symm
  subst hF''e
  obtain ⟨L, hL⟩ := List.getLast?_eq_some_iff.1 hF
  have hFi : F.binds[i]? = some b := by simpa [topBind?, hF] using hb
  have hFi' : F'.binds[i]? = some b' := by simpa [topBind?, he'] using hb'
  have hil : i < F'.binds.length := (List.getElem?_eq_some_iff.1 hFi').1
  have hlen' : F.binds.length = F'.binds.length := by simpa using hlen
  have htop0 : s₀.topIdx = L.length := by
    have := hFR.frames.1; simp only [SState.topIdx]; rw [← this, hL]; simp
  have heq : ∀ j, j ≠ i → F.binds[j]? = F'.binds[j]? := by
    intro j hj
    cases hx : F.binds[j]? with
    | none =>
      have : F.binds.length ≤ j := List.getElem?_eq_none_iff.1 hx
      rw [List.getElem?_eq_none (by omega)]
    | some x =>
      have hlt : j < F.binds.length := (List.getElem?_eq_some_iff.1 hx).1
      obtain ⟨y, hy⟩ : ∃ y, F'.binds[j]? = some y := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hy'' : ({ F' with binds := F'.binds.set i b } : SFrame).binds[j]? = some y := by
        simp only [List.getElem?_set, if_neg (Ne.symm hj)]; exact hy
      rw [hy, bindRen_plain (hbr j x y hx hy'') (hpl j y hj hy)]
  have hselfRen : BindRen σ b b := by
    have hy'' : ({ F' with binds := F'.binds.set i b } : SFrame).binds[i]? = some b := by
      simp only [List.getElem?_set, if_pos hil, if_true]
    exact hbr i b b hFi hy''
  have htemps : F.temps = F'.temps := by
    apply List.ext_getElem?
    intro j
    cases hx : F.temps[j]? with
    | none =>
      have : F.temps.length ≤ j := List.getElem?_eq_none_iff.1 hx
      rw [List.getElem?_eq_none (by simp only at htl; omega)]
    | some v =>
      obtain ⟨v', hv', hvv⟩ := htv j v hx
      simp only at hv'
      rw [hv']
      have hm : v' ∈ F'.temps := List.mem_of_getElem? hv'
      exact congrArg some (funext fun ψ => (hvv ψ).trans (htp v' hm _ _))
  refine ⟨b, b', hb, hb', hself, hselfRen, L, by rw [hL]; simp, htop0, F, F', C, hL, he', ?_, by omega, ?_⟩
  · refine ⟨hlen', hFi, hFi', heq, fun j x hj hx => ?_, htemps, fun v hv => htp v (htemps ▸ hv)⟩
    rw [heq j hj] at hx; exact hpl j x hj hx
  · refine ⟨rfl, rfl, rfl, rfl, rfl, fun p hp => ?_, fun l x hx hp => ?_, hsh', hlt', rfl⟩
    · have := hFR.topShape p (by rw [hp, htop0])
      rw [this]; simp [setTopBind, hsh']
    · obtain ⟨l', rfl⟩ := hFR.lentImg l x (by rw [hp, htop0]) hx
      have := (hFR.lentTop l' x (by rw [hp, htop0])).1 hx
      simp [setTopBind, hlt'] at this

/-- **`FrameRelS` read back off `LF`**, against the relation at the call. -/
theorem lf_end {S S' s s' : SState} {bS bS' : SBinding} {L : List SFrame} {n : Nat}
    (hFR : FrameRel σ s₀ [] S (setTopBind S' i bS)) (hself : SelfRel R bS bS') (hren : BindRen σ bS bS)
    (hL : ∃ F0, S.env = L ++ [F0]) (htop0 : s₀.topIdx = L.length)
    (h : LF i bS bS' L S S' n s s') : FrameRelS R σ s₀ [] i s s' := by
  obtain ⟨F0, hS⟩ := hL
  obtain ⟨F, F', C, he, he', ht, -, hr⟩ := h
  have he'' := setTopBind_env' he' i bS
  have hil : i < F'.binds.length := (List.getElem?_eq_some_iff.1 ht.self').1
  have hlow : ∀ f, f < L.length → s.env[f]? = S.env[f]? := fun f hf => by
    rw [he, hS, List.getElem?_append_left hf, List.getElem?_append_left hf]
  have hshape'' : ∀ p, (setTopBind s' i bS).shape p = none := fun p => hr.shape' p
  have hlent'' : ∀ l, (setTopBind s' i bS).lent l = [] := fun l => hr.lent' l
  have hnl : ∀ l, ¬ (setTopBind s' i bS).Live l := not_live_of_shape hshape''
  refine ⟨bS, bS', by simp [topBind?, he, ht.self], by simp [topBind?, he', ht.self'], hself, ?_⟩
  refine ⟨hFR.inj, fun j => ?_, ⟨?_, ?_⟩, fun f hf => ?_, fun p hp ψ => ?_, fun p hp => ?_, ?_, fun p hp => ?_,
    fun q l hq => ?_, fun l hl => absurd hl (hnl l), fun l x hx => ?_, fun m x hx hm => ?_, fun l x hx => ?_,
    fun l p hp hs => ?_, fun l hl => absurd hl (hnl l)⟩
  · have := hFR.fresh j
    simp only [setTopBind] at this ⊢
    rw [hr.next', hr.next]; exact this
  · rw [he, ← hFR.frames.1, hS]; simp
  · rw [he'']; rfl
  · rw [hlow f (by rw [← htop0]; exact hf)]; exact hFR.lowerSkel f hf
  · rw [valAt_congr_frame (hlow _ (by rw [← htop0]; exact hp))]
    exact hFR.lowerVal p hp ψ
  · rw [hr.shape]; exact hFR.lowerShape p hp
  · refine ⟨F, { F' with binds := F'.binds.set i bS }, by simp [he], by simp [he''], by simp [ht.len],
      fun j x y hx hy => ?_, by simp [ht.temps], fun j v hv => ⟨v, ?_, fun ψ => ?_⟩⟩
    · by_cases hj : j = i
      · subst hj
        rw [ht.self] at hx; cases hx
        simp only [List.getElem?_set, if_pos hil, if_true, Option.some.injEq] at hy
        subst hy; exact hren
      · simp only [List.getElem?_set, if_neg (Ne.symm hj)] at hy
        have hxy : x = y := by rw [ht.eq j hj, hy] at hx; exact (Option.some.inj hx).symm
        subst hxy
        exact bindRen_of_plain σ (ht.plain j x hj hx)
    · simp only; rw [← ht.temps]; exact hv
    · exact ht.tplain v (List.mem_of_getElem? hv) _ _
  · rw [hshape'', hr.shape, hr.topShape p (by rw [hp, htop0])]; rfl
  · rw [hshape''] at hq; cases hq
  · rw [hlent'', hr.lent]
    simp only [List.not_mem_nil, iff_false]
    intro hm; exact hr.topLent _ x hm (by rw [hx, htop0])
  · rw [hr.lent] at hm; exact absurd (by rw [hx, htop0]) (hr.topLent m x hm)
  · rw [hlent''] at hx; cases hx
  · rw [hr.lent]; exact hFR.lentCaller l p hp hs

end

/-! ## The frame property over `FrameRelS` on the label-free fragment -/

section
variable (K : RunCtx) (ρ : Assignment) (φ : Future)

/-- **The frame property, restated over `FrameRelS` (docs/31 D127's ruling), proved on the label-free
fragment** (no parameter label, `ks = []`). From an in-place state `S` and a closure state `S'` related
by `FrameRelS` at the function's own binding `i`, where the closure's state holds no borrow and lends
nothing and its top frame's other bindings and its temporaries are future-free with no label (`n`
bindings after the function's own), a label-free term over those `n` variables (`LFree`) runs, at any
tail flags and hints on the two sides, to the same result and `FrameRelS`-related states, or fails on
both (`FrameAgreeS`). Assumes nothing about the model; of the decision table only that it invalidates
nothing (`noInv`: the fuel-free table's, by definition), and only where the term assigns (`a`). Neither `FundCtx` nor the in-place state's
goodness (`SGood`) nor `FrameStart` is used: the label-free run reaches no whole-state test. -/
theorem run_frameS_lf {a : Bool} (hNI : a = true → ∀ sc p, K.D.invalidated sc p = []) {σ : Nat → Nat} {s₀ : SState} {i n : Nat}
    {S S' : SState} {C F' : SFrame} (hrel : FrameRelS K.dm.read σ s₀ [] i S S')
    (he' : S'.env = [C, F']) (hsh' : ∀ p, S'.shape p = none) (hlt' : ∀ l, S'.lent l = [])
    (hpl : ∀ j b, j ≠ i → F'.binds[j]? = some b → Plain b) (htp : ∀ v ∈ F'.temps, ∀ ψ ψ' : Future, v ψ = v ψ')
    (hn : F'.binds.length = i + 1 + n) {t : Term} (ht : LFree a n t) (tl tl' : Bool) (h h' : TyS) :
    FrameAgreeS K.dm.read σ s₀ [] i (runT K ρ φ tl h t S) (runT K ρ φ tl' h' t S') := by
  obtain ⟨bS, bS', hb, hb', hself, hren, L, -, htop0, hlf⟩ := lf_start hrel he' hsh' hlt' hpl htp hn
  obtain ⟨b, b', hb0, -, -, hFR⟩ := hrel
  rw [hb] at hb0; cases hb0
  have hL : ∃ F0, S.env = L ++ [F0] := by obtain ⟨F0, -, -, hS, -⟩ := hlf; exact ⟨F0, hS⟩
  have hag := lf_run K ρ φ hNI hself.2.2.2.2.1 n t ht S S' tl tl' h h' hlf
  cases hx : runT K ρ φ tl h t S with
  | none =>
    cases hx' : runT K ρ φ tl' h' t S' with
    | none => trivial
    | some y => rw [hx, hx'] at hag; exact hag.elim
  | some y =>
    cases hx' : runT K ρ φ tl' h' t S' with
    | none => rw [hx, hx'] at hag; exact hag.elim
    | some y' =>
      rw [hx, hx'] at hag
      obtain ⟨r, s₁⟩ := y
      obtain ⟨r', s₁'⟩ := y'
      obtain ⟨e, hl, h₁⟩ := hag
      cases e
      refine ⟨rfl, ?_, lf_end hFR hself hren hL htop0 h₁⟩
      obtain ⟨v, T⟩ := r
      cases T with | mk m lab => simp only at hl; subst hl; rfl

end

/-! ## `FrameJ2` holds -/

/-- `I`'s body `S(#0)` is label-free over its one parameter, with no assignment. -/
theorem lfree_bodyI : LFree false 1 bodyI := .succ 1 _ (.var 1 0 (by decide))

/-- **`FrameJ2`, the instance of the frame property `J2`'s step needs, PROVED** (docs/31 D128's model
fact; D129). Assumes nothing: not `FundCtx`, not `FrameStart`, not the in-place state's goodness (the
run of `S(#0)` reads only the parameter, whose binding is the same on both sides, and reaches no
whole-state test). -/
theorem frameJ2_holds : FrameJ2 := by
  intro K ρ φ s₂ f a tl tl' h h' _ _ _ hrel
  refine run_frameS_lf K ρ φ (a := false) (fun e => absurd e (by decide)) hrel (closureJ2_env K.dm.read φ a)
    (closureJ2_shape K.dm.read φ a) (closureJ2_lent K.dm.read φ a) (fun j b hj hb => ?_) (fun v hv => by simp at hv)
    (n := 1) rfl lfree_bodyI tl tl' h h'
  rcases j with _ | _ | j
  · exact absurd rfl hj
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hb
    subst hb; exact ⟨rfl, fun _ _ => rfl⟩
  · simp at hb

open CallBody in
/-- **Steps (3) and (4) of `J2`'s plan with no model fact** (`closureRun_of_checker` with `FrameJ2`
discharged by `frameJ2_holds`): from the checker's callee state related to the in-place reference
state, the closure's run of `I`'s body succeeds with the meaning of the checker's untyped value.
Assumes 2 facts about the checker, `BodyLazyInv` and `InvNumA`; no model fact. -/
theorem closureRun_of_checker_free (hB : BodyLazyInv) (hN : InvNumA)
    {K : RunCtx} {ρ : Assignment} {φ : Future} {R : List DeclInfo} (hd : ParDecI K.D R) (hc : Strict.FundCtx K)
    {s₂ : SState} {f : Sem} {a : Nat} {st st' : MState} {n : Nat} {hint : Option Value} {bh : Nat} {v : Value}
    {T? : Option Value} {π : Nat → Nat}
    (hP : LazyNum K ρ R st) (hm : Mode st) (hp : Pre K ρ st)
    (hr : Rel K ρ φ π st (inPlaceJ2 K.dm.read s₂ f a)) (hS : Strict.SGood K.dm K.Γ φ (inPlaceJ2 K.dm.read s₂ f a))
    (hfs : FrameStart (inPlaceJ2 K.dm.read s₂ f a) [])
    (hrel : FrameRelS K.dm.read (fun l => s₂.nextLoan + l) (inPlaceJ2 K.dm.read s₂ f a) [] 0
      (inPlaceJ2 K.dm.read s₂ f a) (closureJ2 K.dm.read φ a))
    (hfl : K.D.flags (scopeOf (inPlaceJ2 K.dm.read s₂ f a)) bodyI = (false, false)) (hcd : CallBody.CopyDec K.D st (.var 0))
    (h : Runs (Ochr.eval n false bodyI hint) st bh (v, T?) st') (tl : Bool) (h' : TyS) :
    ∃ (ρ' : Assignment) (Δ' : Nat → TyS) (π' : Nat → Nat) (r : Res) (s' : SState),
      runT K ρ φ tl h' bodyI (closureJ2 K.dm.read φ a) = some (r, s') ∧
      ∃ T : TyS, meanV { K with Δ := Δ' } ρ' (fun l => φ (π' l)) T v = r.1 :=
  closureRun_of_checker hB hN frameJ2_holds hd hc hP hm hp hr hS hfs hrel hfl hcd h tl h'

/-! ## The frame property restated over `FrameRelS`: the general statement (open) -/

/-- **The frame property, restated over `FrameRelS`** (docs/31 D127's ruling; D129's locality clause), as
a named proposition: OPEN in general, proved on the label-free fragment (`run_frameS_lf`, whose
hypotheses imply these). For every context with `FundCtx`, from an in-place state `s` and a closure state
`s'` related by `FrameRelS` at the function's own binding `i` (not read by `t`: its de Bruijn index in the
closure's top frame is not free in `t`), with the in-place state good and `FrameStart` met at the call,
the closure's positions reading only its live labels and its top frame none of the parameters' (the
clause D129 adds: without it the statement is false, `Strict/FrameLocCE.run_frame_loc_false`), a term with
no `Id` (or a call with no parameter label) runs to the same result, its label renamed, and related
states, or fails on both sides.

What a proof needs beyond the label-free fragment, clause by clause of `runT` (docs/31 D129): `&x` and
`x := u`/`*y := u` with a label: [End] (`endLabel`) and [Access] (`access`, its rounds) on related states,
the typed futures related through `σ` (the locality clause), the strict end tests (`EndOk`, `AccessOk`)
equivalent; `let`/`;` ending a held borrow (the same); a field path: the whole-state test (`StateOk`),
the caller's frames by `SGood` and `FrameStart` (they read no label of the frame), the closure's own by
the relation; `match`: `movedPlaces` (top frame, at `lentFuture`), the entry and the join's drop; `.fix`
inside the body: the inner closure's runs from states with one more frame (`FrameRel.frames` asks two)
and its meaning's equality (its finals read through `σ`, equal where they read only the returned label);
`.call`: `callOf` on related states (the consumed arguments' fixing, `mapVals`, reaching the caller's
frames only through parameter labels); `Id` with parameters: `run_frame_obs`. -/
def RunFrameS : Prop :=
  ∀ (K : RunCtx) (ρ : Assignment) (φ : Future) (σ : Nat → Nat) (s₀ : SState) (ks : List Nat) (i : Nat)
    (tl : Bool) (hint : TyS) (t : Term) (s s' : SState),
    Strict.FundCtx K → FrameStart s₀ ks → t.valsOk (Strict.ValsP K ρ φ) → (t.idFree = true ∨ ks = []) →
    (∀ F', s'.env.getLast? = some F' → (F'.binds.length - 1 - i) ∉ t.freeVars) →
    FrameRelS K.dm.read σ s₀ ks i s s' →
    (∀ p, Ochr.Meaning.FT (fun l => s'.Live l) (s'.valAt p)) →
    (∀ p, p.frameOf = 1 → Ochr.Meaning.FT (fun l => s'.Live l ∧ σ l ∉ ks) (s'.valAt p)) →
    Strict.SGood K.dm K.Γ φ s →
    FrameAgreeS K.dm.read σ s₀ ks i (runT K ρ φ tl hint t s) (runT K ρ φ tl hint t s')

end FrameFrag

end Ochr.Meaning.Steps.Form
