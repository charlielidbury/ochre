import OchrMeta.GuardBF

/-! # Lemma 1 for borrow-free programs: symbolic runs approximate actual runs

`VR θ v w`: the symbolic value `v` approximates the actual value `w`, where `θ` instantiates the
abstract values.  `Z`, `S` and pairs must match; an abstract value `σₐ` stands exactly for `θ a`;
everything the symbolic run cannot branch on without getting stuck or erring is a wildcard:
sealed programs (closed-off calls, whose actual counterpart is whatever the call computed), `()`
(also the result of a closed-off call at `Unit`), `⋆` and `⊥`.

`sim_exec`: if the machine run of a borrow-free term completes on a symbolic state, its run on
any approximated actual state completes with an approximated result, or errs, or runs out of
fuel, but is never stuck.  This covers the calls the checker makes to other functions. -/

namespace OchrMeta

def VR (θ : Nat → Val) : Val → Val → Prop
  | .abs a, w => w = θ a
  | .zero, w => w = .zero
  | .succ v, w => ∃ w', w = .succ w' ∧ VR θ v w'
  | .pair a b, w => ∃ c d, w = .pair c d ∧ VR θ a c ∧ VR θ b d
  | .unit, _ => True
  | .star, _ => True
  | .moved, _ => True
  | .sealed .., _ => True
  | .borrow .., _ => False
  | .loan _, _ => False

/-- Frames with the same variables, values approximated. -/
inductive FR (θ : Nat → Val) : Frame → Frame → Prop
  | nil : FR θ [] []
  | cons {x : Var} {v w : Val} {F G : Frame} : VR θ v w → FR θ F G → FR θ ((x, v) :: F) ((x, w) :: G)

/-- Lists of values, approximated pointwise. -/
inductive VRs (θ : Nat → Val) : List Val → List Val → Prop
  | nil : VRs θ [] []
  | cons {v w : Val} {vs ws : List Val} : VR θ v w → VRs θ vs ws → VRs θ (v :: vs) (w :: ws)

theorem VRs.length {θ : Nat → Val} {vs ws : List Val} (h : VRs θ vs ws) : vs.length = ws.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem FR.lookup {θ : Nat → Val} {F G : Frame} (h : FR θ F G) {x : Var} {v : Val}
    (hv : F.lookup x = some v) : ∃ w, G.lookup x = some w ∧ VR θ v w := by
  induction h with
  | nil => simp at hv
  | @cons y v' w' F G hvw _ ih =>
    simp only [List.lookup] at hv ⊢
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv
      exact ⟨w', rfl, hvw⟩
    · exact ih hv

theorem FR.set {θ : Nat → Val} {F G : Frame} (h : FR θ F G) (x : Var) {v w : Val} (hv : VR θ v w) :
    FR θ (F.set x v) (G.set x w) := by
  induction h with
  | nil => exact FR.nil
  | @cons y v' w' F G hvw hrest ih =>
    simp only [Frame.set]
    split
    · exact FR.cons hv hrest
    · exact FR.cons hvw ih

theorem FR.remove {θ : Nat → Val} {F G : Frame} (h : FR θ F G) {x : Var} {v : Val} {F' : Frame}
    (hv : F.remove x = some (v, F')) : ∃ w G', G.remove x = some (w, G') ∧ VR θ v w ∧ FR θ F' G' := by
  induction h generalizing F' with
  | nil => simp [Frame.remove] at hv
  | @cons y v' w' F G hvw hrest ih =>
    simp only [Frame.remove] at hv ⊢
    split at hv
    · simp only [Option.some.injEq, Prod.mk.injEq] at hv; obtain ⟨rfl, rfl⟩ := hv
      rename_i hxy; simp only [hxy, if_true]; exact ⟨w', G, rfl, hvw, hrest⟩
    · rename_i hxy; simp only [hxy, if_false]
      obtain ⟨⟨v1, F1⟩, hr, he⟩ := Option.map_eq_some_iff.mp hv
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      obtain ⟨w1, G1, hr', hvw1, hF1⟩ := ih hr
      exact ⟨w1, (y, w') :: G1, by simp [hr'], hvw1, FR.cons hvw hF1⟩

theorem VR.step {θ : Nat → Val} {v w : Val} (h : VR θ v w) {pr : Proj} {v' : Val}
    (hs : pr.step v = .ok v') : ∃ w', pr.step w = .ok w' ∧ VR θ v' w' := by
  cases pr <;> cases v <;> simp_all [Proj.step, Val.isNeutral, VR] <;> (try split at hs) <;>
    (try simp_all) <;> (try (obtain ⟨w', rfl, h⟩ := h; subst_vars; exact ⟨_, rfl, by assumption⟩)) <;>
    (try (obtain ⟨c, d, rfl, h1, h2⟩ := h; subst_vars; first | exact ⟨_, rfl, h1⟩ | exact ⟨_, rfl, h2⟩))

theorem VR.getR {θ : Nat → Val} : ∀ {v w : Val} {π : List Proj} {c : Val}, VR θ v w → v.getR π = .ok c →
    ∃ c', w.getR π = .ok c' ∧ VR θ c c'
  | v, w, [], c, h, hg => by simp only [Val.getR, StepRes.ok.injEq] at hg; subst hg; exact ⟨w, rfl, h⟩
  | v, w, pr :: ps, c, h, hg => by
    simp only [Val.getR] at hg ⊢
    split at hg
    · rename_i v' hv'
      obtain ⟨w', hw', h'⟩ := h.step hv'
      rw [hw']
      exact VR.getR h' hg
    · cases hg
    · cases hg

theorem VR.put {θ : Nat → Val} {v w new new' v' v₀ : Val} (h : VR θ v w) (hn : VR θ new new') {pr : Proj}
    (hs : pr.step v = .ok v₀) (hp : pr.put v new = some v') : ∃ w', pr.put w new' = some w' ∧ VR θ v' w' := by
  cases pr <;> cases v <;> simp_all [Proj.step, Proj.put, Val.isNeutral, VR] <;> (try split at hs) <;>
    (try simp_all)
  · obtain ⟨w', rfl, _⟩ := h; subst_vars; exact ⟨_, rfl, _, rfl, hn⟩
  · obtain ⟨c, d, rfl, _, h2⟩ := h; subst_vars; exact ⟨_, rfl, _, _, rfl, hn, h2⟩
  · obtain ⟨c, d, rfl, h1, _⟩ := h; subst_vars; exact ⟨_, rfl, _, _, rfl, h1, hn⟩

theorem VR.set {θ : Nat → Val} : ∀ {v w : Val} {π : List Proj} {new new' v' : Val}, VR θ v w → VR θ new new' →
    v.set π new = some v' → ∃ w', w.set π new' = some w' ∧ VR θ v' w'
  | v, w, [], new, new', v', _, hn, hs => by
    simp only [Val.set, Option.some.injEq] at hs; subst hs; exact ⟨new', rfl, hn⟩
  | v, w, pr :: ps, new, new', v', h, hn, hs => by
    simp only [Val.set] at hs ⊢
    split at hs
    · rename_i v₀ hv₀
      obtain ⟨w₀, hw₀, h₀⟩ := h.step hv₀
      simp only [hw₀]
      obtain ⟨v₁, hv₁, hput⟩ := Option.bind_eq_some_iff.mp hs
      obtain ⟨w₁, hw₁, h₁⟩ := VR.set h₀ hn hv₁
      obtain ⟨w', hw', h'⟩ := VR.put h h₁ hv₀ hput
      exact ⟨w', by simp only [hw₁, Option.bind_some]; exact hw', h'⟩
    all_goals cases hs

theorem access_sim {θ : Nat → Val} {N N' : Nat} {F G : Frame} {Ω Ω' : Env} {k k' : Nat} (hF : BFSt N F Ω)
    (hG : BFSt N' G Ω') (hFG : FR θ F G) {deep : Bool} {x : Var} {π : List Proj} {s' : St} {c : Val}
    (h : access deep x π ⟨F :: Ω, k⟩ = .ok s' c) :
    ∃ c', access deep x π ⟨G :: Ω', k'⟩ = .ok ⟨G :: Ω', k'⟩ c' ∧ VR θ c c' := by
  rw [access_nb hF.env_nb] at h
  rw [access_nb hG.env_nb]
  simp only [St.lookup, List.head?_cons, Option.bind_some] at h ⊢
  split at h
  · cases h
  · rename_i v hv
    obtain ⟨w, hw, hvw⟩ := hFG.lookup hv
    simp only [hw]
    split at h
    · rename_i c₀ hc
      simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨c', hc', h'⟩ := hvw.getR hc
      simp only [hc']
      exact ⟨c', rfl, h'⟩
    all_goals cases h

theorem setPlace_sim {θ : Nat → Val} {F G : Frame} {Ω Ω' : Env} {k k' : Nat} (hFG : FR θ F G)
    {x : Var} {π : List Proj} {v w : Val} (hvw : VR θ v w) {s' : St}
    (h : St.setPlace x π v ⟨F :: Ω, k⟩ = some s') :
    ∃ F' G', s' = ⟨F' :: Ω, k⟩ ∧ St.setPlace x π w ⟨G :: Ω', k'⟩ = some ⟨G' :: Ω', k'⟩ ∧ FR θ F' G' := by
  simp only [St.setPlace, St.lookup, List.head?_cons, Option.bind_some] at h ⊢
  obtain ⟨c, hc, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨d, hd, hcd⟩ := hFG.lookup hc
  obtain ⟨d', hd', h'⟩ := VR.set hcd hvw hc'
  refine ⟨F.set x c', G.set x d', rfl, ?_, hFG.set x h'⟩
  rw [hd]; simp only [Option.bind_some, hd', Option.map_some]; rfl

theorem takeTemps_sim {θ : Nat → Val} {Ω Ω' : Env} {k k' : Nat} : ∀ (is : List Nat) {F G : Frame}
    {ws : List Val} {s' : St}, FR θ F G → takeTemps is ⟨F :: Ω, k⟩ = some (ws, s') →
    ∃ F' G' ws', s' = ⟨F' :: Ω, k⟩ ∧ takeTemps is ⟨G :: Ω', k'⟩ = some (ws', ⟨G' :: Ω', k'⟩) ∧
      VRs θ ws ws' ∧ FR θ F' G'
  | [], F, G, ws, s', hFG, h => by
    simp only [takeTemps, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨F, G, [], rfl, rfl, VRs.nil, hFG⟩
  | i :: is, F, G, ws, s', hFG, h => by
    simp only [takeTemps] at h ⊢
    obtain ⟨⟨v, s1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [St.unbind] at h1
    obtain ⟨⟨v', F1⟩, hr, he⟩ := Option.map_eq_some_iff.mp h1
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨w, G1, hr', hvw, hFG1⟩ := hFG.remove hr
    obtain ⟨⟨vs, s2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
    simp only [Prod.mk.injEq] at h4; obtain ⟨rfl, rfl⟩ := h4
    obtain ⟨F2, G2, ws', rfl, h5, hws, hFG2⟩ := takeTemps_sim (Ω' := Ω') (k' := k') is hFG1 h3
    refine ⟨F2, G2, w :: ws', rfl, ?_, VRs.cons hvw hws, hFG2⟩
    simp only [St.unbind, hr', Option.map_some, Option.bind_some, h5]

theorem paramFrame_sim {θ : Nat → Val} : ∀ (ps : List Var) {ws ws' : List Val}, VRs θ ws ws' →
    FR θ (ps.zip ws) (ps.zip ws')
  | [], _, _, _ => by simp; exact FR.nil
  | _ :: _, [], [], _ => by simp; exact FR.nil
  | x :: ps, w :: ws, w' :: ws', VRs.cons h hs => by
    simp only [List.zip_cons_cons]; exact FR.cons h (paramFrame_sim ps hs)

/-! ## Approximated runs -/

/-- The actual result approximates a completed symbolic run ending in `⟨F₁ :: _, _⟩` with value
`v`: it completes with an approximated top frame and value, or errs, or runs out of fuel; it is
never stuck. -/
def SimOk (θ : Nat → Val) (F₁ : Frame) (v : Val) (Ω' : Env) (k' : Nat) : Res → Prop
  | .ok c w => ∃ G₁, c = ⟨G₁ :: Ω', k'⟩ ∧ FR θ F₁ G₁ ∧ VR θ v w
  | .stuck => False
  | .err => True
  | .oof => True

/-- An evaluator whose completed symbolic runs are approximated by its actual runs. -/
def SimEv (θ : Nat → Val) (ev : St → Term → Res) : Prop :=
  ∀ (N N' : Nat) (F G : Frame) (Ω Ω' : Env) (k k' : Nat) (t : Term) (F₁ : Frame) (v : Val),
    t.noBorrow = true → BFSt N F Ω → BFSt N' G Ω' → FR θ F G →
    ev ⟨F :: Ω, k⟩ t = .ok ⟨F₁ :: Ω, k⟩ v → SimOk θ F₁ v Ω' k' (ev ⟨G :: Ω', k'⟩ t)

theorem sim_execArgs {θ : Nat → Val} {ev : St → Term → Res} (hev : SimEv θ ev) (hbf : EvBF ev)
    {N N' : Nat} {Ω Ω' : Env} {k k' : Nat} : ∀ (args : List Term) (i : Nat) (F G F₁ : Frame) (v : Val),
    (∀ a ∈ args, a.noBorrow = true) → BFSt N F Ω → BFSt N' G Ω' → FR θ F G →
    execArgs ev i ⟨F :: Ω, k⟩ args = .ok ⟨F₁ :: Ω, k⟩ v → SimOk θ F₁ v Ω' k' (execArgs ev i ⟨G :: Ω', k'⟩ args)
  | [], i, F, G, F₁, v, _, _, _, hFG, h => by
    simp only [execArgs, Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
    obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
    exact ⟨G, rfl, hFG, trivial⟩
  | a :: as, i, F, G, F₁, v, hb, hF, hG, hFG, h => by
    simp only [execArgs] at h ⊢
    cases h1 : ev ⟨F :: Ω, k⟩ a with
    | ok s1 w1 =>
      rw [h1, Res.bind_ok] at h
      obtain ⟨F2, rfl, hF2, hw1⟩ := hbf N F Ω k a s1 w1 (hb a (by simp)) hF h1
      have hs := hev N N' F G Ω Ω' k k' a F2 w1 (hb a (by simp)) hF hG hFG h1
      cases h2 : ev ⟨G :: Ω', k'⟩ a with
      | ok c1 w1' =>
        rw [h2] at hs
        obtain ⟨G2, rfl, hFG2, hvw⟩ := hs
        obtain ⟨G2', he, hG2, hw1'⟩ := hbf N' G Ω' k' a _ w1' (hb a (by simp)) hG h2
        simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
        rw [Res.bind_ok]
        exact sim_execArgs hev hbf as (i + 1) _ _ F₁ v (fun b hb' => hb b (List.mem_cons_of_mem _ hb'))
          (hF2.cons hw1) (hG2.cons hw1') (FR.cons hvw hFG2) h
      | stuck => rw [h2] at hs; exact hs.elim
      | err => trivial
      | oof => trivial
    | _ => rw [h1] at h; cases h

theorem closeCall_ne_stuck (f : String) (d : FunDef) (ws : List Val) (s : St) : closeCall f d ws s ≠ .stuck := by
  unfold closeCall
  split
  · simp
  · simp only
    split
    · simp
    · split
      · split
        · simp
        · split <;> simp
      · split <;> simp
      · split <;> simp

theorem callWith_cc_ne_stuck {ev : St → Term → Res} {f : String} {d : FunDef} {ws : List Val} {s : St} :
    callWith ev true f d ws s ≠ .stuck := by
  unfold callWith
  split
  · exact closeCall_ne_stuck f d ws s
  · split
    · split
      · split <;> simp
      · exact closeCall_ne_stuck f d ws s
      · simp
      · simp
    · simp

/-- The wildcards: the results of a closed-off call. -/
theorem VR.wild {θ : Nat → Val} {f : String} {ws : List Val} {v : Val}
    (h : v = .unit ∨ ∃ k, v = .sealed f (Val.ofList ws) k .unit) (w : Val) : VR θ v w := by
  rcases h with rfl | ⟨_, rfl⟩ <;> trivial

theorem closeCall_sim {θ : Nat → Val} {h : String} {d : FunDef} (hd : d.BF) {F G : Frame} {Ω' : Env}
    {k' : Nat} (hFG : FR θ F G) {v : Val} (hv : ∀ w, VR θ v w) (ws' : List Val) :
    SimOk θ F v Ω' k' (closeCall h d ws' ⟨G :: Ω', k'⟩) := by
  cases hc : closeCall h d ws' ⟨G :: Ω', k'⟩ with
  | ok c w => obtain ⟨rfl, _⟩ := closeCall_bf hd hc; exact ⟨G, rfl, hFG, hv w⟩
  | stuck => exact closeCall_ne_stuck _ _ _ _ hc
  | err => trivial
  | oof => trivial

theorem sim_callWith {θ : Nat → Val} {ev : St → Term → Res} (hev : SimEv θ ev) (hbf : EvBF ev)
    {cc : Bool} {h : String} {d : FunDef} (hd : d.BF) {N N' : Nat} {F G : Frame} {Ω Ω' : Env} {k k' : Nat}
    {ws ws' : List Val} (hF : BFSt N F Ω) (hG : BFSt N' G Ω') (hFG : FR θ F G)
    (hws : ∀ w ∈ ws, BFVal N w) (hws' : ∀ w ∈ ws', BFVal N' w) (hvs : VRs θ ws ws') {s₁ : St} {v : Val}
    (hc : callWith ev cc h d ws ⟨F :: Ω, k⟩ = .ok s₁ v) :
    s₁ = ⟨F :: Ω, k⟩ ∧ SimOk θ F v Ω' k' (callWith ev cc h d ws' ⟨G :: Ω', k'⟩) := by
  obtain ⟨rfl, _⟩ := callWith_bf hbf hd hF hws hc
  refine ⟨rfl, ?_⟩
  unfold callWith at hc ⊢
  cases hb : d.body with
  | none =>
    rw [hb] at hc; simp only at hc ⊢
    cases cc
    · simp at hc
    · simp only [if_true] at hc ⊢
      exact closeCall_sim hd hFG (VR.wild (closeCall_bf hd hc).2) ws'
  | some b =>
    rw [hb] at hc; simp only at hc ⊢
    split at hc
    · rename_i hlen
      rw [if_pos (by rw [← hvs.length]; exact hlen)]
      have hp := paramFrame_bf (N := N) d (d.params.map Prod.fst) ws hws
      have hp' := paramFrame_bf (N := N') d (d.params.map Prod.fst) ws' hws'
      have hPF : BFSt N (paramFrame d ws) (F :: Ω) := ⟨hp.1, hF.env_nb, hp.2⟩
      have hPG : BFSt N' (paramFrame d ws') (G :: Ω') := ⟨hp'.1, hG.env_nb, hp'.2⟩
      have hPFG : FR θ (paramFrame d ws) (paramFrame d ws') := paramFrame_sim _ hvs
      have e : St.push (paramFrame d ws') ⟨G :: Ω', k'⟩ = ⟨paramFrame d ws' :: G :: Ω', k'⟩ := rfl
      rw [e]
      split at hc
      · rename_i s2 v2 hr
        obtain ⟨F2, rfl, hF2, hv2⟩ := hbf N (paramFrame d ws) (F :: Ω) k b s2 v2 (hd.body b hb) hPF hr
        rw [popFrame_bf hv2.1 F2 (F :: Ω) k (by simp only [Env.nb, hF2.top, hF.top, hF.rest])] at hc
        simp only [Res.ok.injEq] at hc; obtain ⟨-, rfl⟩ := hc
        have hs := hev N N' _ _ (F :: Ω) (G :: Ω') k k' b F2 v2 (hd.body b hb) hPF hPG hPFG hr
        cases hr' : ev ⟨paramFrame d ws' :: G :: Ω', k'⟩ b with
        | ok c2 w2 =>
          have hs' : SimOk θ F2 v2 (G :: Ω') k' (.ok c2 w2) := hr' ▸ hs
          obtain ⟨G2, rfl, _, hvw⟩ := hs'
          obtain ⟨G2', he, hG2, hw2⟩ := hbf N' _ (G :: Ω') k' b _ w2 (hd.body b hb) hPG hr'
          simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
          simp only
          rw [popFrame_bf hw2.1 G2 (G :: Ω') k' (by simp only [Env.nb, hG2.top, hG.top, hG.rest])]
          exact ⟨G, rfl, hFG, hvw⟩
        | stuck => rw [hr'] at hs; exact hs.elim
        | err => simp [SimOk]
        | oof => simp [SimOk]
      · split at hc
        · rename_i hcc
          subst hcc
          have hv := VR.wild (θ := θ) (closeCall_bf hd hc).2
          cases hr' : ev ⟨paramFrame d ws' :: G :: Ω', k'⟩ b with
          | ok c2 w2 =>
            obtain ⟨G2', he, hG2, hw2⟩ := hbf N' _ (G :: Ω') k' b _ w2 (hd.body b hb) hPG hr'
            subst he
            simp only
            rw [popFrame_bf hw2.1 G2' (G :: Ω') k' (by simp only [Env.nb, hG2.top, hG.top, hG.rest])]
            exact ⟨G, rfl, hFG, hv w2⟩
          | stuck => simp only [if_true]; exact closeCall_sim hd hFG hv ws'
          | err => simp [SimOk]
          | oof => simp [SimOk]
        · cases hc
      · cases hc
      · cases hc
    · cases hc

theorem SimOk.of_ok {θ : Nat → Val} {F₁ G₁ : Frame} {v w : Val} {Ω' : Env} {k' : Nat}
    (h1 : FR θ F₁ G₁) (h2 : VR θ v w) : SimOk θ F₁ v Ω' k' (.ok ⟨G₁ :: Ω', k'⟩ w) := ⟨G₁, rfl, h1, h2⟩

/-- Continue after an approximated sub-run. -/
theorem SimOk.bind {θ : Nat → Val} {F₁ : Frame} {v : Val} {Ω' : Env} {k' : Nat} {r : Res}
    (h : SimOk θ F₁ v Ω' k' r) {K : St → Val → Res} {Q : Res → Prop}
    (hK : ∀ G₁ w, FR θ F₁ G₁ → VR θ v w → r = .ok ⟨G₁ :: Ω', k'⟩ w → Q (K ⟨G₁ :: Ω', k'⟩ w))
    (herr : Q .err) (hoof : Q .oof) : Q (r.bind K) := by
  cases r with
  | ok c w => obtain ⟨G₁, rfl, h1, h2⟩ := h; exact hK G₁ w h1 h2 rfl
  | stuck => exact h.elim
  | err => exact herr
  | oof => exact hoof

/-- **Symbolic runs are approximated by actual runs** (borrow-free fragment). -/
theorem sim_exec {P : Prog} (hP : P.BF) (θ : Nat → Val) : ∀ n, SimEv θ (exec P n) := by
  intro n
  induction n with
  | zero => intro N N' F G Ω Ω' k k' t F₁ v _ _ _ _ h; simp [exec] at h
  | succ n ih =>
    intro N N' F G Ω Ω' k k' t F₁ v ht hF hG hFG h
    cases t with
    | read p =>
      simp only [exec] at h ⊢
      cases ha : access true p.root p.path ⟨F :: Ω, k⟩ with
      | ok s1 c =>
        rw [ha, Res.bind_ok] at h
        obtain ⟨rfl, hc⟩ := access_bf hF ha
        obtain ⟨c', ha', hcc⟩ := access_sim (k' := k') hF hG hFG ha
        obtain ⟨-, hc'⟩ := access_bf hG ha'
        rw [ha', Res.bind_ok]
        split at h
        · cases h
        · simp [BFVal, Val.nb] at hc
        · simp only [Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
          obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
          split
          · simp [SimOk]
          · simp [BFVal, Val.nb] at hc'
          · exact SimOk.of_ok hFG hcc
      | _ => rw [ha] at h; cases h
    | borrow p => simp [Term.noBorrow] at ht
    | assign p t =>
      simp only [exec] at h ⊢
      simp only [Term.noBorrow] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F2, rfl, hF2, hv1⟩ := exec_bf hP n N F Ω k t s1 v1 ht hF h1
        refine SimOk.bind (ih N N' F G Ω Ω' k k' t F2 v1 ht hF hG hFG h1)
          (fun G2 w1 hFG2 hvw h2 => ?_) trivial trivial
        obtain ⟨G2', he, hG2, hw1⟩ := exec_bf hP n N' G Ω' k' t _ w1 ht hG h2
        simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
        cases ha : access true p.root p.path ⟨F2 :: Ω, k⟩ with
        | ok s3 c =>
          rw [ha, Res.bind_ok] at h
          obtain ⟨rfl, hc⟩ := access_bf hF2 ha
          obtain ⟨c', ha', hcc⟩ := access_sim (k' := k') hF2 hG2 hFG2 ha
          obtain ⟨-, hc'⟩ := access_bf hG2 ha'
          rw [ha', Res.bind_ok]
          rw [if_neg (fun hh => hh.2 hv1.1)] at h
          rw [if_neg (fun hh => hh.2 hw1.1)]
          split at h
          · cases h
          · rename_i s4 hs4
            obtain ⟨F4, G4, rfl, hs4', hFG4⟩ := setPlace_sim (Ω' := Ω') (k' := k') hFG2 hvw hs4
            obtain ⟨F4', he4, hF4⟩ := setPlace_bf hF2 hv1 hs4
            simp only [St.mk.injEq, List.cons.injEq] at he4; obtain ⟨⟨rfl, -⟩, -⟩ := he4
            obtain ⟨G4', he4', hG4⟩ := setPlace_bf hG2 hw1 hs4'
            simp only [St.mk.injEq, List.cons.injEq] at he4'; obtain ⟨⟨rfl, -⟩, -⟩ := he4'
            rw [dropVal_bf hF4.env_nb rfl hc.1] at h
            simp only [Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
            obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
            rw [hs4']; dsimp only
            rw [dropVal_bf hG4.env_nb rfl hc'.1]
            exact SimOk.of_ok hFG4 trivial
        | _ => rw [ha] at h; cases h
      | _ => rw [h1] at h; cases h
    | letIn x t u =>
      simp only [exec] at h ⊢
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F2, rfl, hF2, hv1⟩ := exec_bf hP n N F Ω k t s1 v1 ht.1 hF h1
        refine SimOk.bind (ih N N' F G Ω Ω' k k' t F2 v1 ht.1 hF hG hFG h1)
          (fun G2 w1 hFG2 hvw h2 => ?_) trivial trivial
        obtain ⟨G2', he, hG2, hw1⟩ := exec_bf hP n N' G Ω' k' t _ w1 ht.1 hG h2
        simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
        have e : St.bind x v1 ⟨F2 :: Ω, k⟩ = ⟨((x, v1) :: F2) :: Ω, k⟩ := rfl
        have e' : St.bind x w1 ⟨G2 :: Ω', k'⟩ = ⟨((x, w1) :: G2) :: Ω', k'⟩ := rfl
        rw [e] at h; rw [e']
        cases h3 : exec P n ⟨((x, v1) :: F2) :: Ω, k⟩ u with
        | ok s3 v3 =>
          rw [h3, Res.bind_ok] at h
          obtain ⟨F3, rfl, hF3, hv3⟩ := exec_bf hP n N _ Ω k u s3 v3 ht.2 (hF2.cons hv1) h3
          refine SimOk.bind (ih N N' _ _ Ω Ω' k k' u F3 v3 ht.2 (hF2.cons hv1) (hG2.cons hw1)
            (FR.cons hvw hFG2) h3) (fun G3 w3 hFG3 hvw3 h4 => ?_) trivial trivial
          obtain ⟨G3', he3, hG3, hw3⟩ := exec_bf hP n N' _ Ω' k' u _ w3 ht.2 (hG2.cons hw1) h4
          simp only [St.mk.injEq, List.cons.injEq] at he3; obtain ⟨⟨rfl, -⟩, -⟩ := he3
          split at h
          · cases h
          · rename_i c s5 hu
            obtain ⟨F5, rfl, hF5, hc⟩ := unbind_bf hF3 hu
            simp only [St.unbind] at hu
            obtain ⟨⟨c0, F5'⟩, hr, he5⟩ := Option.map_eq_some_iff.mp hu
            simp only [Prod.mk.injEq, St.mk.injEq, List.cons.injEq] at he5
            obtain ⟨rfl, ⟨rfl, -⟩, -⟩ := he5
            obtain ⟨c', G5, hr', hcc, hFG5⟩ := hFG3.remove hr
            have hu' : St.unbind x ⟨G3 :: Ω', k'⟩ = some (c', ⟨G5 :: Ω', k'⟩) := by
              simp [St.unbind, hr']
            obtain ⟨G5', he5', hG5, hc'⟩ := unbind_bf hG3 hu'
            simp only [St.mk.injEq, List.cons.injEq] at he5'; obtain ⟨⟨rfl, -⟩, -⟩ := he5'
            rw [dropVal_bf hF5.env_nb hv3.1 hc.1] at h
            simp only [Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
            obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
            rw [hu']; dsimp only
            rw [dropVal_bf hG5.env_nb hw3.1 hc'.1]
            exact SimOk.of_ok hFG5 hvw3
        | _ => rw [h3] at h; cases h
      | _ => rw [h1] at h; cases h
    | seq t u =>
      simp only [exec] at h ⊢
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F2, rfl, hF2, hv1⟩ := exec_bf hP n N F Ω k t s1 v1 ht.1 hF h1
        refine SimOk.bind (ih N N' F G Ω Ω' k k' t F2 v1 ht.1 hF hG hFG h1)
          (fun G2 w1 hFG2 hvw h2 => ?_) trivial trivial
        obtain ⟨G2', he, hG2, hw1⟩ := exec_bf hP n N' G Ω' k' t _ w1 ht.1 hG h2
        simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
        rw [dropVal_bf hF2.env_nb rfl hv1.1] at h
        rw [dropVal_bf hG2.env_nb rfl hw1.1]
        exact ih N N' F2 G2 Ω Ω' k k' u F₁ v ht.2 hF2 hG2 hFG2 h
      | _ => rw [h1] at h; cases h
    | zero =>
      simp only [exec, Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h ⊢
      obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h; exact SimOk.of_ok hFG rfl
    | unit =>
      simp only [exec, Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h ⊢
      obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h; exact SimOk.of_ok hFG trivial
    | erase t =>
      simp only [exec, Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h ⊢
      obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h; exact SimOk.of_ok hFG trivial
    | succ t =>
      simp only [exec] at h ⊢
      simp only [Term.noBorrow] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F2, rfl, hF2, hv1⟩ := exec_bf hP n N F Ω k t s1 v1 ht hF h1
        refine SimOk.bind (ih N N' F G Ω Ω' k k' t F2 v1 ht hF hG hFG h1)
          (fun G2 w1 hFG2 hvw h2 => ?_) trivial trivial
        obtain ⟨G2', he, hG2, hw1⟩ := exec_bf hP n N' G Ω' k' t _ w1 ht hG h2
        simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
        rw [if_pos hv1.1] at h
        simp only [Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
        obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
        rw [if_pos hw1.1]
        exact SimOk.of_ok hFG2 ⟨w1, rfl, hvw⟩
      | _ => rw [h1] at h; cases h
    | pair t u =>
      simp only [exec] at h ⊢
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases h1 : exec P n ⟨F :: Ω, k⟩ t with
      | ok s1 v1 =>
        rw [h1, Res.bind_ok] at h
        obtain ⟨F2, rfl, hF2, hv1⟩ := exec_bf hP n N F Ω k t s1 v1 ht.1 hF h1
        refine SimOk.bind (ih N N' F G Ω Ω' k k' t F2 v1 ht.1 hF hG hFG h1)
          (fun G2 w1 hFG2 hvw h2 => ?_) trivial trivial
        obtain ⟨G2', he, hG2, hw1⟩ := exec_bf hP n N' G Ω' k' t _ w1 ht.1 hG h2
        simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
        cases h3 : exec P n ⟨F2 :: Ω, k⟩ u with
        | ok s3 v3 =>
          rw [h3, Res.bind_ok] at h
          obtain ⟨F3, rfl, hF3, hv3⟩ := exec_bf hP n N F2 Ω k u s3 v3 ht.2 hF2 h3
          refine SimOk.bind (ih N N' F2 G2 Ω Ω' k k' u F3 v3 ht.2 hF2 hG2 hFG2 h3)
            (fun G3 w3 hFG3 hvw3 h4 => ?_) trivial trivial
          obtain ⟨G3', he3, hG3, hw3⟩ := exec_bf hP n N' G2 Ω' k' u _ w3 ht.2 hG2 h4
          simp only [St.mk.injEq, List.cons.injEq] at he3; obtain ⟨⟨rfl, -⟩, -⟩ := he3
          rw [if_pos ⟨hv1.1, hv3.1⟩] at h
          simp only [Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
          obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
          rw [if_pos ⟨hw1.1, hw3.1⟩]
          exact SimOk.of_ok hFG3 ⟨w1, w3, rfl, hvw, hvw3⟩
        | _ => rw [h3] at h; cases h
      | _ => rw [h1] at h; cases h
    | mtch p tz y ts =>
      simp only [exec] at h ⊢
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      cases ha : access false p.root p.path ⟨F :: Ω, k⟩ with
      | ok s1 c =>
        rw [ha, Res.bind_ok] at h
        obtain ⟨rfl, hc⟩ := access_bf hF ha
        obtain ⟨c', ha', hcc⟩ := access_sim (k' := k') hF hG hFG ha
        rw [ha', Res.bind_ok]
        cases c with
        | zero =>
          simp only [VR] at hcc; subst hcc
          exact ih N N' F G Ω Ω' k k' tz F₁ v ht.1 hF hG hFG h
        | succ c0 =>
          obtain ⟨w0, rfl, _⟩ := hcc
          exact ih N N' F G Ω Ω' k k' _ F₁ v (by rw [Term.noBorrow_substVar]; exact ht.2) hF hG hFG h
        | _ => simp only at h; split at h <;> cases h
      | _ => rw [ha] at h; cases h
    | call f args cc =>
      simp only [exec] at h ⊢
      cases hf : P.find f with
      | none => rw [hf] at h; cases h
      | some d =>
        rw [hf] at h; simp only at h ⊢
        split at h
        · rename_i hp
          simp only [hp, if_true]
          simp only [Res.ok.injEq, St.mk.injEq, List.cons.injEq] at h
          obtain ⟨⟨⟨rfl, -⟩, -⟩, rfl⟩ := h
          exact SimOk.of_ok hFG trivial
        · rename_i hp
          simp only [hp, if_false]
          have hbl := Term.noBorrowList_iff.mp (by simpa [Term.noBorrow] using ht)
          cases h1 : execArgs (exec P n) 0 ⟨F :: Ω, k⟩ args with
          | ok s1 v1 =>
            rw [h1, Res.bind_ok] at h
            obtain ⟨F2, rfl, hF2⟩ := execArgs_bf (exec_bf hP n) args 0 F s1 v1 hbl hF h1
            refine SimOk.bind (sim_execArgs ih (exec_bf hP n) args 0 F G F2 v1 hbl hF hG hFG h1)
              (fun G2 w1 hFG2 _ h2 => ?_) trivial trivial
            obtain ⟨G2', he, hG2⟩ := execArgs_bf (exec_bf hP n) args 0 G _ w1 hbl hG h2
            simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
            split at h
            · cases h
            · rename_i ws s3 htt
              obtain ⟨F3, G3, ws', rfl, htt', hvs, hFG3⟩ := takeTemps_sim (Ω' := Ω') (k' := k') _ hFG2 htt
              obtain ⟨F3', he3, hF3, hws⟩ := takeTemps_bf _ F2 ws _ hF2 htt
              simp only [St.mk.injEq, List.cons.injEq] at he3; obtain ⟨⟨rfl, -⟩, -⟩ := he3
              obtain ⟨G3', he3', hG3, hws'⟩ := takeTemps_bf _ G2 ws' _ hG2 htt'
              simp only [St.mk.injEq, List.cons.injEq] at he3'; obtain ⟨⟨rfl, -⟩, -⟩ := he3'
              rw [htt']
              obtain ⟨he4, hs4⟩ := sim_callWith ih (exec_bf hP n) (hP f d hf) hF3 hG3 hFG3 hws hws' hvs h
              simp only [St.mk.injEq, List.cons.injEq] at he4; obtain ⟨⟨rfl, -⟩, -⟩ := he4
              exact hs4
          | _ => rw [h1] at h; cases h

end OchrMeta
