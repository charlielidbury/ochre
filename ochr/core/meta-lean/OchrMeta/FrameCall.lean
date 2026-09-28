import OchrMeta.FrameOps2

/-! # Frame lemma, part 3: arguments, temporaries, [Close], [Call] -/

namespace OchrMeta

section
variable {Ω₂ : Env} {K : List Nat}

/-- An evaluator commutes with `frameMap` and keeps the port-side shape. -/
def EvF (Ω₂ : Env) (K : List Nat) (ev : St → Term → Res) : Prop :=
  ∀ (c : St) (P : Frame) (t : Term), PInv Ω₂ K c P →
    ev (c.app (Ω₂.substPorts P)) t = (ev (c.app [P]) t).map (frameMap Ω₂) ∧
    PRes Ω₂ K c.env.length (ev (c.app [P]) t)

theorem PInv.bind {c : St} {P : Frame} (hc : PInv Ω₂ K c P) (x : Var) {v : Val}
    (hv : ∀ l ∈ v.names, Good Ω₂ K l) : PInv Ω₂ K (c.bind x v) P := by
  refine hc.grow (S := fun l => l ∈ v.names) ?_ hv (fun y hy => St.names_bind y hy) ?_
  · obtain ⟨Ω, m⟩ := c; cases Ω with
    | nil => exact absurd rfl hc.ne
    | cons F Ω => simp [St.bind, St.modTop]
  · obtain ⟨Ω, m⟩ := c; cases Ω <;> simp [St.bind, St.modTop]

theorem St.length_bind {c : St} (hc : c.env ≠ []) (x : Var) (v : Val) : (c.bind x v).env.length = c.env.length := by
  obtain ⟨Ω, m⟩ := c; cases Ω with
  | nil => exact absurd rfl hc
  | cons F Ω => simp [St.bind, St.modTop]

theorem execArgs_frame {ev : St → Term → Res} (hev : EvF Ω₂ K ev) :
    ∀ (args : List Term) (i : Nat) (c : St) (P : Frame), PInv Ω₂ K c P →
      execArgs ev i (c.app (Ω₂.substPorts P)) args = (execArgs ev i (c.app [P]) args).map (frameMap Ω₂) ∧
      PRes Ω₂ K c.env.length (execArgs ev i (c.app [P]) args) := by
  intro args
  induction args with
  | nil => intro i c P hc; exact ⟨by simp [execArgs, St.frameMap_app], c, P, rfl, hc, rfl, by simp [Val.names]⟩
  | cons a as ih =>
    intro i c P hc
    simp only [execArgs]
    obtain ⟨h1, h2⟩ := hev c P a hc
    rw [h1]
    cases hr : ev (c.app [P]) a with
    | ok s v =>
      rw [hr] at h2
      obtain ⟨c', P', rfl, hc', hlen, hv⟩ := h2
      simp only [Res.map_ok, Res.bind_ok, St.frameMap_app]
      rw [St.bind_app _ hc'.ne, St.bind_app _ hc'.ne]
      have := ih (i + 1) (c'.bind (.tmp i) v) P' (hc'.bind _ hv)
      rw [St.length_bind hc'.ne, hlen] at this
      exact this
    | stuck => exact ⟨rfl, trivial⟩
    | err => exact ⟨rfl, trivial⟩
    | oof => exact ⟨rfl, trivial⟩

theorem takeTemps_frame :
    ∀ (is : List Nat) (c : St) (P : Frame), PInv Ω₂ K c P →
      takeTemps is (c.app (Ω₂.substPorts P)) =
        (takeTemps is (c.app [P])).map (fun p => (p.1, frameMap Ω₂ p.2)) ∧
      ∀ vs s', takeTemps is (c.app [P]) = some (vs, s') →
        ∃ c' P', s' = c'.app [P'] ∧ PInv Ω₂ K c' P' ∧ c'.env.length = c.env.length ∧
          c'.next = c.next ∧ ∀ v ∈ vs, ∀ l ∈ v.names, Good Ω₂ K l := by
  intro is
  induction is with
  | nil =>
    intro c P hc
    refine ⟨by simp [takeTemps, St.frameMap_app], ?_⟩
    intro vs s' h; simp [takeTemps] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨c, P, rfl, hc, rfl, rfl, by simp⟩
  | cons i is ih =>
    intro c P hc
    simp only [takeTemps, St.unbind_app _ hc.ne]
    cases hu : c.unbind (.tmp i) with
    | none => exact ⟨rfl, by simp⟩
    | some p =>
      obtain ⟨v, c1⟩ := p
      obtain ⟨hn1, hnv, hl1, hx1⟩ := St.unbind_spec hu
      have hc1 : PInv Ω₂ K c1 P := hc.shrink (Env.ne_nil_of_length hl1 hc.ne) hn1 (hx1 ▸ Nat.le_refl _)
      simp only [Option.map_some, Option.bind_some]
      obtain ⟨ih1, ih2⟩ := ih c1 P hc1
      rw [ih1]
      refine ⟨?_, ?_⟩
      · cases takeTemps is (c1.app [P]) <;> rfl
      · intro vs s' h
        cases ht : takeTemps is (c1.app [P]) with
        | none => rw [ht] at h; simp at h
        | some q =>
          obtain ⟨vs', s''⟩ := q
          rw [ht] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨c', P', rfl, hc', hl', hx', hvs⟩ := ih2 vs' _ ht
          refine ⟨c', P', rfl, hc', hl'.trans hl1, hx'.trans hx1, ?_⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact fun l hl => hc.good l (hnv l hl)
          · exact hvs w hw

theorem sealArgs_spec : ∀ (i : Nat) (ps : List (Var × Ty)) (ws : List Val) (as : List Val)
    (ls : List (Nat × Nat)), sealArgs i ps ws = some (as, ls) →
      (∀ a ∈ as, ∀ x ∈ a.names, ∃ w ∈ ws, x ∈ w.names) ∧ (∀ p ∈ ls, ∃ w ∈ ws, p.2 ∈ w.names) := by
  intro i ps
  induction ps generalizing i with
  | nil =>
    intro ws as ls h
    cases ws with
    | nil => simp [sealArgs] at h; obtain ⟨rfl, rfl⟩ := h; simp
    | cons w ws => simp [sealArgs] at h
  | cons p ps ih =>
    intro ws as ls h
    obtain ⟨y, ty⟩ := p
    cases ws with
    | nil => cases ty <;> simp [sealArgs] at h
    | cons w ws =>
      cases ty with
      | ref T =>
        cases w with
        | borrow l u =>
          simp only [sealArgs] at h
          cases hr : sealArgs (i + 1) ps ws with
          | none => rw [hr] at h; cases h
          | some q =>
            obtain ⟨as', ls'⟩ := q
            rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
            obtain ⟨h1, h2⟩ := ih (i + 1) ws as' ls' hr
            refine ⟨?_, ?_⟩
            · intro a ha x hx
              rcases List.mem_cons.mp ha with rfl | ha
              · exact ⟨.borrow l a, by simp, by simp [Val.names, hx]⟩
              · obtain ⟨w', hw', hx'⟩ := h1 a ha x hx; exact ⟨w', List.mem_cons_of_mem _ hw', hx'⟩
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact ⟨.borrow l u, by simp, by simp [Val.names]⟩
              · obtain ⟨w', hw', hx'⟩ := h2 q hq; exact ⟨w', List.mem_cons_of_mem _ hw', hx'⟩
        | _ => simp [sealArgs] at h
      | _ =>
        simp only [sealArgs] at h
        cases hr : sealArgs (i + 1) ps ws with
        | none => rw [hr] at h; cases h
        | some q =>
          obtain ⟨as', ls'⟩ := q
          rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨h1, h2⟩ := ih (i + 1) ws as' ls' hr
          refine ⟨?_, ?_⟩
          · intro a ha x hx
            rcases List.mem_cons.mp ha with rfl | ha
            · exact ⟨a, by simp, hx⟩
            · obtain ⟨w', hw', hx'⟩ := h1 a ha x hx; exact ⟨w', List.mem_cons_of_mem _ hw', hx'⟩
          · intro q hq
            obtain ⟨w', hw', hx'⟩ := h2 q hq; exact ⟨w', List.mem_cons_of_mem _ hw', hx'⟩

theorem Val.names_ofList {as : List Val} {x : Nat} (h : x ∈ (Val.ofList as).names) : ∃ a ∈ as, x ∈ a.names := by
  induction as with
  | nil => simp [Val.ofList, Val.names] at h
  | cons a as ih =>
    simp only [Val.ofList, Val.names, List.mem_append] at h
    rcases h with h | h
    · exact ⟨a, by simp, h⟩
    · obtain ⟨b, hb, hx⟩ := ih h; exact ⟨b, List.mem_cons_of_mem _ hb, hx⟩

theorem fillLoans_frame :
    ∀ (fs : List (Nat × Val)) (c : St) (P : Frame), PInv Ω₂ K c P →
      (∀ p ∈ fs, Good Ω₂ K p.1 ∧ ∀ x ∈ p.2.names, Good Ω₂ K x) →
      fillLoans fs (c.app (Ω₂.substPorts P)) = (fillLoans fs (c.app [P])).map (frameMap Ω₂) ∧
      PSt Ω₂ K c.env.length c.next (fillLoans fs (c.app [P])) := by
  intro fs
  induction fs with
  | nil => intro c P hc _; exact ⟨by simp [fillLoans, St.frameMap_app], c, P, rfl, hc, rfl, Nat.le_refl _⟩
  | cons p fs ih =>
    intro c P hc hfs
    obtain ⟨l, w⟩ := p
    simp only [fillLoans]
    have hp := hfs (l, w) (by simp)
    rw [endWith_frame w hc hp.1]
    cases he : endWith l w (c.app [P]) with
    | none => exact ⟨rfl, trivial⟩
    | some s' =>
      obtain ⟨c', P', rfl, hc', hlen, hnx⟩ := endWith_pinv hc hp.2 he
      simp only [Option.map_some, Option.bind_some, St.frameMap_app]
      obtain ⟨h1, h2⟩ := ih c' P' hc' (fun q hq => hfs q (List.mem_cons_of_mem _ hq))
      refine ⟨h1, ?_⟩
      cases hf : fillLoans fs (c'.app [P']) with
      | none => trivial
      | some s'' =>
        rw [hf] at h2
        obtain ⟨c'', P'', rfl, hc'', hl'', hn''⟩ := h2
        exact ⟨c'', P'', rfl, hc'', hl''.trans hlen, hnx ▸ hn''⟩

theorem PInv.bump {c : St} {P : Frame} (hc : PInv Ω₂ K c P) : PInv Ω₂ K ⟨c.env, c.next + 1⟩ P :=
  hc.shrink hc.ne (fun _ h => h) (Nat.le_succ _)

theorem closeCall_frame (f : String) (d : FunDef) {ws : List Val} {c : St} {P : Frame}
    (hc : PInv Ω₂ K c P) (hws : ∀ w ∈ ws, ∀ l ∈ w.names, Good Ω₂ K l) :
    closeCall f d ws (c.app (Ω₂.substPorts P)) = (closeCall f d ws (c.app [P])).map (frameMap Ω₂) ∧
    PRes Ω₂ K c.env.length (closeCall f d ws (c.app [P])) := by
  unfold closeCall
  cases hsa : sealArgs 0 d.params ws with
  | none => exact ⟨rfl, trivial⟩
  | some q =>
    obtain ⟨as, ls⟩ := q
    obtain ⟨has, hls⟩ := sealArgs_spec 0 d.params ws as ls hsa
    have hargs : ∀ x ∈ (Val.ofList as).names, Good Ω₂ K x := by
      intro x hx
      obtain ⟨a, ha, hxa⟩ := Val.names_ofList hx
      obtain ⟨w, hw, hxw⟩ := has a ha x hxa
      exact hws w hw x hxw
    have hl : ∀ p ∈ ls, Good Ω₂ K p.2 := by
      intro p hp; obtain ⟨w, hw, hx⟩ := hls p hp; exact hws w hw p.2 hx
    simp only
    by_cases hnb : (Val.ofList as).nb ≠ 0
    · rw [if_pos hnb, if_pos hnb]; exact ⟨rfl, trivial⟩
    rw [if_neg hnb, if_neg hnb]
    -- the fills for the borrow-free rows
    have hfin : ∀ p ∈ ls.map (fun (q : Nat × Nat) => (q.2, Val.sealed f (Val.ofList as) (.fin q.1) .unit)),
        Good Ω₂ K p.1 ∧ ∀ x ∈ p.2.names, Good Ω₂ K x := by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      refine ⟨hl q hq, ?_⟩
      intro x hx
      simp only [Val.names, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hargs x hx
      · simp at hx
    cases hret : d.ret with
    | ref T =>
      simp only
      by_cases hls : ls = []
      · rw [if_pos hls, if_pos hls]; exact ⟨rfl, trivial⟩
      rw [if_neg hls, if_neg hls]
      have hk : Good Ω₂ K c.next := hc.fresh _ (Nat.le_refl _)
      have hback : ∀ p ∈ ls.map (fun (q : Nat × Nat) =>
          (q.2, Val.sealed f (Val.ofList as) (.back q.1) (.loan c.next))),
          Good Ω₂ K p.1 ∧ ∀ x ∈ p.2.names, Good Ω₂ K x := by
        intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        refine ⟨hl q hq, ?_⟩
        intro x hx
        simp only [Val.names, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hargs x hx
        · exact hk
      have e1 : ({ c.app (Ω₂.substPorts P) with next := c.next + 1 } : St) =
          (⟨c.env, c.next + 1⟩ : St).app (Ω₂.substPorts P) := rfl
      have e2 : ({ c.app [P] with next := c.next + 1 } : St) = (⟨c.env, c.next + 1⟩ : St).app [P] := rfl
      simp only [St.app_next] at e1 e2 ⊢
      rw [e1, e2]
      obtain ⟨h1, h2⟩ := fillLoans_frame _ ⟨c.env, c.next + 1⟩ P hc.bump hback
      rw [h1]
      cases hf : fillLoans _ ((⟨c.env, c.next + 1⟩ : St).app [P]) with
      | none => exact ⟨rfl, trivial⟩
      | some s2 =>
        rw [hf] at h2
        obtain ⟨c', P', rfl, hc', hlen, _⟩ := h2
        refine ⟨by simp [St.frameMap_app], c', P', rfl, hc', hlen, ?_⟩
        intro x hx
        simp only [Val.names, List.mem_cons, List.mem_append] at hx
        rcases hx with rfl | hx | hx
        · exact hk
        · exact hargs x hx
        · simp at hx
    | unit =>
      simp only
      obtain ⟨h1, h2⟩ := fillLoans_frame _ c P hc hfin
      rw [h1]
      cases hf : fillLoans _ (c.app [P]) with
      | none => exact ⟨rfl, trivial⟩
      | some s2 =>
        rw [hf] at h2
        obtain ⟨c', P', rfl, hc', hlen, _⟩ := h2
        exact ⟨by simp [St.frameMap_app], c', P', rfl, hc', hlen, by simp [Val.names]⟩
    | _ =>
      simp only
      obtain ⟨h1, h2⟩ := fillLoans_frame _ c P hc hfin
      rw [h1]
      cases hf : fillLoans _ (c.app [P]) with
      | none => exact ⟨rfl, trivial⟩
      | some s2 =>
        rw [hf] at h2
        obtain ⟨c', P', rfl, hc', hlen, _⟩ := h2
        refine ⟨by simp [St.frameMap_app], c', P', rfl, hc', hlen, ?_⟩
        intro x hx
        simp only [Val.names, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hargs x hx
        · simp at hx

theorem paramFrame_names {d : FunDef} {ws : List Val} {b : Var × Val} (hb : b ∈ paramFrame d ws)
    {x : Nat} (hx : x ∈ b.2.names) : ∃ w ∈ ws, x ∈ w.names :=
  ⟨b.2, List.of_mem_zip hb |>.2, hx⟩

theorem PInv.push {c : St} {P : Frame} (hc : PInv Ω₂ K c P) (F : Frame)
    (hF : ∀ b ∈ F, ∀ l ∈ b.2.names, Good Ω₂ K l) : PInv Ω₂ K (c.push F) P := by
  refine hc.grow (by simp [St.push]) (S := fun l => ∃ b ∈ F, l ∈ b.2.names)
    (fun x ⟨b, hb, hx⟩ => hF b hb x hx) ?_ (Nat.le_refl _)
  intro x hx
  simp only [St.push, Env.mem_names] at hx ⊢
  obtain ⟨G, hG, b, hb, hxb⟩ := hx
  rcases List.mem_cons.mp hG with rfl | hG
  · exact Or.inr ⟨b, hb, hxb⟩
  · exact Or.inl ⟨G, hG, b, hb, hxb⟩

theorem callWith_frame {run : St → Term → Res} (hrun : EvF Ω₂ K run) (cc : Bool) (f : String)
    (d : FunDef) {ws : List Val} {c : St} {P : Frame}
    (hc : PInv Ω₂ K c P) (hws : ∀ w ∈ ws, ∀ l ∈ w.names, Good Ω₂ K l) :
    callWith run cc f d ws (c.app (Ω₂.substPorts P)) = (callWith run cc f d ws (c.app [P])).map (frameMap Ω₂) ∧
    PRes Ω₂ K c.env.length (callWith run cc f d ws (c.app [P])) := by
  unfold callWith
  cases hb : d.body with
  | none =>
    simp only
    split
    · exact closeCall_frame f d hc hws
    · exact ⟨rfl, trivial⟩
  | some b =>
    simp only
    split
    · have hc1 : PInv Ω₂ K (c.push (paramFrame d ws)) P :=
        hc.push _ (fun b hb l hl => by
          obtain ⟨w, hw, hx⟩ := paramFrame_names hb hl; exact hws w hw l hx)
      rw [St.push_app, St.push_app]
      obtain ⟨h1, h2⟩ := hrun _ P b hc1
      rw [h1]
      cases hr : run ((c.push (paramFrame d ws)).app [P]) b with
      | ok s' v =>
        rw [hr] at h2
        obtain ⟨c', P', rfl, hc', hlen, hv⟩ := h2
        simp only [Res.map_ok, St.frameMap_app]
        have h2c : 2 ≤ c'.env.length := by
          rw [hlen]; simp only [St.push, List.length_cons]
          have := List.length_pos_iff.mpr hc.ne; omega
        obtain ⟨p1, p2⟩ := popFrame_frame v hc' h2c
        rw [p1]
        cases hp : popFrame v (c'.app [P']) with
        | none => exact ⟨rfl, trivial⟩
        | some s'' =>
          rw [hp] at p2
          obtain ⟨c'', P'', rfl, hc'', hl'', _⟩ := p2
          refine ⟨by simp [St.frameMap_app], c'', P'', rfl, hc'', ?_, hv⟩
          rw [hl'', hlen]; simp [St.push]
      | stuck =>
        simp only [Res.map_stuck]
        split
        · exact closeCall_frame f d hc hws
        · exact ⟨rfl, trivial⟩
      | err => exact ⟨rfl, trivial⟩
      | oof => exact ⟨rfl, trivial⟩
    · exact ⟨rfl, trivial⟩

end
end OchrMeta
