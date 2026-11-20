import Ochr.Meaning.Steps.BotWriteGood

/-!
# The checker's typing of places after the drop's write of `⊥` (the slice, `ctx_botWrite`)

The write replaces one part of one position's value by `⊥`. Every place's content after it is the
old content (a place off the written path), `⊥` (the written place), or the old content with `⊥`
written strictly inside it (a place above the written one): the same head, so the same answer to
what a declared inductive admits (`fitsInd`), and never `⋆`. A place below the written one does not
exist after it. The frames' shapes and the bindings' declared readings are unchanged, and so are
the records and the unknowns' types and readings. So every clause of `ShapeFacts` survives
(`ShapeFacts.of_botWrite`).
-/

namespace Ochr.Meaning.Steps.Slice

open Ochr Ochr.Meaning Ochr.Meaning.Steps

/-- **A content after the write of `⊥` was a content before**: the old one, or the old one with `⊥`
written at a path inside it (the empty path: the written `⊥` itself). -/
theorem follow_updAt_bot_any : ∀ (steps : List Step) (v v' : Value), Value.updAt (fun _ => .bot) steps v = some v' →
    ∀ path u, v'.follow path = some u →
      ∃ u₀, v.follow path = some u₀ ∧ (u = u₀ ∨ ∃ ss, Value.updAt (fun _ => .bot) ss u₀ = some u)
  | [], v, v', h, path, u, hf => by
    simp only [Value.updAt, Option.some.injEq] at h; subst h
    cases path with
    | nil =>
      simp only [Value.follow, Option.some.injEq] at hf; subst hf
      exact ⟨v, rfl, .inr ⟨[], by simp [Value.updAt]⟩⟩
    | cons s ps => simp [Value.follow, stepV] at hf
  | st :: ss, v, v', h, path, u, hf => by
    cases path with
    | nil =>
      simp only [Value.follow, Option.some.injEq] at hf; subst hf
      exact ⟨v, rfl, .inr ⟨st :: ss, h⟩⟩
    | cons s ps =>
    cases v with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [follow_gloan_cons] at hf ⊢
      exact follow_updAt_bot_any (st :: ss) w w' hw' (s :: ps) u hf
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
        cases s with
        | deref =>
          simp only [Value.follow, stepV, Option.bind_some] at hf ⊢
          exact follow_updAt_bot_any ss w w' hw' ps u hf
        | proj _ | field _ => simp [Value.follow, stepV] at hf
      | proj _ | field _ => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
          cases s with
          | proj j =>
            cases j with
            | zero =>
              simp only [Value.follow, stepV, Option.bind_some] at hf ⊢
              exact follow_updAt_bot_any ss w w' hw' ps u hf
            | succ _ => simp [Value.follow, stepV] at hf
          | deref | field _ => simp [Value.follow, stepV] at hf
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps' fs =>
      obtain ⟨i, w, w', hci, hw, hw', rfl⟩ : ∃ i w w', st.key = some (c, i) ∧ fs[i]? = some w ∧
          Value.updAt (fun _ => .bot) ss w = some w' ∧ v' = .ind ty c hh ps' (fs.set i w') := by
        cases st with
        | deref => simp [Value.updAt] at h
        | proj i =>
          cases c with
          | succ _ => simp [Value.updAt] at h
          | zero =>
            simp only [Value.updAt] at h
            split at h
            · rename_i w hw
              obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
              exact ⟨i, w, w', rfl, hw, hw', rfl⟩
            · cases h
        | field g =>
          simp only [Value.updAt] at h
          split at h
          · rename_i w hw
            obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
            split at hw
            · rename_i hc
              simp only [Bool.and_eq_true, beq_iff_eq] at hc
              exact ⟨g.idx, w, w', by simp [Step.key, hc.2], hw, hw', rfl⟩
            · cases hw
          · cases h
      simp only [Value.follow] at hf ⊢
      obtain ⟨u₁, hu₁, hfu⟩ := Option.bind_eq_some_iff.mp hf
      rcases stepV_ind_set s ty c hh ps' fs i w w' hw u₁ hu₁ with h1 | ⟨-, rfl, h1⟩
      · exact ⟨u, by rw [h1, Option.bind_some]; exact hfu, .inl rfl⟩
      · obtain ⟨u₀, hu₀, hrel⟩ := follow_updAt_bot_any ss w u₁ hw' ps u hfu
        exact ⟨u₀, by rw [h1, Option.bind_some]; exact hu₀, hrel⟩
    | _ => simp [Value.updAt] at h
termination_by steps v => (steps.length, sizeOf v)

/-- **`⊥` written strictly inside keeps the head**: what a declared inductive admits is unchanged,
and the value is not `⋆`. -/
theorem updAt_bot_head : ∀ (ss : List Step) (u₀ u : Value), Value.updAt (fun _ => .bot) ss u₀ = some u → ss ≠ [] →
    (∀ n, u.fitsInd n = u₀.fitsInd n) ∧ u ≠ .proof
  | [], _, _, _, hne => (hne rfl).elim
  | st :: ss, u₀, u, h, _ => by
    cases u₀ with
    | gloan m w =>
      simp only [Value.updAt] at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      have ih := updAt_bot_head (st :: ss) w w' hw' (List.cons_ne_nil _ _)
      exact ⟨fun n => by simp only [Value.fitsInd, ih.1 n], fun h => by cases h⟩
    | borrow m w =>
      cases st with
      | deref =>
        simp only [Value.updAt] at h
        obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨fun _ => rfl, fun h => by cases h⟩
      | proj _ | field _ => simp [Value.updAt] at h
    | succ w =>
      cases st with
      | proj i =>
        cases i with
        | zero =>
          simp only [Value.updAt] at h
          obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨fun _ => rfl, fun h => by cases h⟩
        | succ _ => simp [Value.updAt] at h
      | deref | field _ => simp [Value.updAt] at h
    | ind ty c hh ps fs =>
      cases st with
      | deref => simp [Value.updAt] at h
      | proj i =>
        cases c with
        | succ _ => simp [Value.updAt] at h
        | zero =>
          simp only [Value.updAt] at h
          split at h
          · obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
            exact ⟨fun _ => rfl, fun h => by cases h⟩
          · cases h
      | field g =>
        simp only [Value.updAt] at h
        split at h
        · obtain ⟨w', -, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨fun _ => rfl, fun h => by cases h⟩
        · cases h
    | _ => simp [Value.updAt] at h
termination_by ss u₀ => (ss.length, sizeOf u₀)

/-! ## The frames' shapes and readings after a write -/

theorem frame_modify_binds (fr : Frame) (i : Nat) (v : Value) :
    ({ fr with binds := fr.binds.modify i ({ · with val := v }) } : Frame).binds.toList.map (·.decl) =
      fr.binds.toList.map (·.decl) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
    split <;> rfl

/-- The write keeps every frame's number of bindings and their declared readings. -/
theorem frame_setAtE (env : Env) (pos : Pos) (v : Value) (f : Nat) :
    ((Env.setAtE env pos v)[f]?).map (fun fr => fr.binds.toList.map (·.decl)) =
      (env[f]?).map (fun fr => fr.binds.toList.map (·.decl)) := by
  cases pos with
  | bind f' i =>
    simp only [Env.setAtE, Array.getElem?_modify]
    by_cases h : f' = f
    · subst h; simp only [if_true]
      cases env[f']? with
      | none => rfl
      | some fr => simp only [Option.map_some]; exact congrArg some (frame_modify_binds fr i v)
    · simp only [h, if_false]
  | temp f' i =>
    simp only [Env.setAtE, Array.getElem?_modify]
    by_cases h : f' = f
    · subst h; simp only [if_true]; cases env[f']? <;> rfl
    · simp only [h, if_false]

theorem size_setAtE (env : Env) (pos : Pos) (v : Value) : (Env.setAtE env pos v).size = env.size := by
  cases pos <;> simp [Env.setAtE]

theorem ckVarPos_setAtE (env : Env) (pos : Pos) (v : Value) (i : Nat) :
    ckVarPos (Env.setAtE env pos v) i = ckVarPos env i := by
  have e := frame_setAtE env pos v (env.size - 1)
  have hn : ∀ (e' : Env), e'[e'.size - 1]!.binds.size =
      (((e'[e'.size - 1]?).map (fun (fr : Frame) => fr.binds.toList.map (·.decl))).getD []).length := by
    intro e'
    rw [getElem!_def]
    cases h : e'[e'.size - 1]? with
    | none => simp; rfl
    | some fr => simp
  unfold ckVarPos
  rw [hn, hn, size_setAtE, e]

theorem topReadings_setAtE (st : MState) (pos : Pos) (v : Value) :
    DecideScope.topReadings { st with env := Env.setAtE st.env pos v } = DecideScope.topReadings st := by
  unfold DecideScope.topReadings
  simp only [Array.back?, size_setAtE]
  rw [frame_setAtE]

/-! ## The typing of places -/

/-- **A content after the write was a content before** (`follow_updAt_bot_any` at the checker's
place lookup, which the write does not change). -/
theorem ckContent_setAtE_bot {env : Env} {pos : Pos} {steps : List Step} {v' : Value} (hp : pos ∈ allPos env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt env pos) = some v') {p : Place} {u : Value}
    (h : ckContent (Env.setAtE env pos v') p = some u) :
    ∃ u₀, ckContent env p = some u₀ ∧ (u = u₀ ∨ ∃ ss, Value.updAt (fun _ => .bot) ss u₀ = some u) := by
  unfold ckContent at h ⊢
  rw [ckVarPos_setAtE] at h
  cases hc : ckVarPos env p.steps.1 with
  | none => rw [hc] at h; cases h
  | some q =>
    rw [hc] at h; simp only [Option.bind_some] at h ⊢
    by_cases hq : q = pos
    · subst hq
      rw [valAt_setAtE_self v' hp] at h
      exact follow_updAt_bot_any steps _ v' hv p.steps.2 u h
    · rw [valAt_setAtE_other env pos q v' hq] at h
      exact ⟨u, h, .inl rfl⟩

/-- **The checker's typing of places survives the drop's write of `⊥`** (`ShapeFacts.of_botWrite`):
(V) a content after is the old one, `⊥`, or the old one with the same head; (L) the loans are a
part of the old ones and their liveness is unchanged (`hlive`, the borrows held are); (N) the write
adds no constructor value; (C⋆) `⋆` after was `⋆` before at the same place; the readings, the
records and the unknowns' types and readings are untouched. -/
theorem ShapeFacts.of_botWrite {D : Decisions} {Γ : List IndDecl} {st : MState} {pos : Pos}
    {steps : List Step} {v' : Value}
    (hf : ShapeFacts D Γ st) (hp : pos ∈ allPos st.env)
    (hv : Value.updAt (fun _ => .bot) steps (valAt st.env pos) = some v')
    (hlive : ∀ l, liveLoan (Env.setAtE st.env pos v') l = liveLoan st.env l) :
    ShapeFacts D Γ { st with env := Env.setAtE st.env pos v' } := by
  have e1 := topReadings_setAtE st pos v'
  refine ⟨?_, ?_, ?_, ?_, hf.etaHint, hf.etaNoSelf, hf.readingsSorted⟩
  · intro p u n args hu hd hn
    rw [e1] at hd
    obtain ⟨u₀, hu₀, hrel⟩ := ckContent_setAtE_bot hp hv hu
    have old := hf.fits p u₀ n args hu₀ hd hn
    rcases hrel with rfl | ⟨ss, hss⟩
    · exact old
    · rcases ss with _ | ⟨x, ss⟩
      · simp only [Value.updAt, Option.some.injEq] at hss; subst hss; rfl
      · rw [(updAt_bot_head _ _ _ hss (List.cons_ne_nil _ _)).1 n]; exact old
  · intro w hw l hl
    rw [hlive]
    rcases mem_values_setAtE hw with rfl | hw
    · exact hf.loans _ (List.mem_map.mpr ⟨pos, hp, rfl⟩) l ((loans_updAt_bot _ _ _ hv).subset hl)
    · exact hf.loans w hw l hl
  · exact values_anyAtom_setAtE (shallow_dataCtorBad Γ) hp hv hf.ctors
  · intro p hgr hu
    rw [e1] at hgr ⊢
    obtain ⟨u₀, hu₀, hrel⟩ := ckContent_setAtE_bot hp hv hu
    rcases hrel with h0 | ⟨ss, hss⟩
    · exact hf.proofCopy p hgr (h0 ▸ hu₀)
    · rcases ss with _ | ⟨x, ss⟩
      · simp [Value.updAt] at hss
      · exact absurd rfl (updAt_bot_head _ _ _ hss (List.cons_ne_nil _ _)).2

end Ochr.Meaning.Steps.Slice
