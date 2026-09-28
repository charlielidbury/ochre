import OchrMeta.GuardSim

/-! # Lemma 1 for borrow-free programs: the checker's branches cover the actual run

`sim_gexec`: if the checker's run of a body passes (every branch), then the actual run of the
body from any approximated state terminates, and if it completes, its final state and value are
approximated by one of the checker's branches, under an extension of the instantiation `θ` (each
[Split] the actual run passes through fixes the fresh predecessor `σ'` to the actual predecessor).
At a recursive call the guard gives an argument strictly smaller than the entry value, so the
call terminates by the induction hypothesis on the entry value; a call to another function
terminates by the call order.  The assembly into Lemma 1 is at the end. -/

namespace OchrMeta
open Guard

/-! ## The checker's results -/

namespace Guard.GRes

theorem app_ok {a b : GRes} {cs : List (GSt × Val)} (h : a.app b = .ok cs) :
    ∃ xs ys, a = .ok xs ∧ b = .ok ys ∧ cs = xs ++ ys := by
  cases a <;> cases b <;> simp_all [GRes.app]

theorem bindList_ok {k : GSt → Val → GRes} : ∀ {bs : List (GSt × Val)} {cs : List (GSt × Val)},
    bindList k bs = .ok cs → ∀ p ∈ bs, ∃ cs', k p.1 p.2 = .ok cs' ∧ ∀ x ∈ cs', x ∈ cs
  | [], _, _, p, hp => by simp at hp
  | (g, v) :: bs, cs, h, p, hp => by
    simp only [bindList] at h
    obtain ⟨xs, ys, h1, h2, rfl⟩ := app_ok h
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨xs, h1, fun x hx => List.mem_append_left _ hx⟩
    · obtain ⟨cs', h3, h4⟩ := bindList_ok h2 p hp
      exact ⟨cs', h3, fun x hx => List.mem_append_right _ (h4 x hx)⟩

theorem bind_ok {r : GRes} {k : GSt → Val → GRes} {cs : List (GSt × Val)} (h : r.bind k = .ok cs) :
    ∃ bs, r = .ok bs ∧ ∀ p ∈ bs, ∃ cs', k p.1 p.2 = .ok cs' ∧ ∀ x ∈ cs', x ∈ cs := by
  cases r with
  | ok bs => exact ⟨bs, rfl, bindList_ok h⟩
  | rej _ => simp [GRes.bind] at h

theorem lift_ok {g : GSt} {r : Res} {bs : List (GSt × Val)} (h : GRes.lift g r = .ok bs) :
    ∃ s v, r = .ok s v ∧ bs = [(g.withSt s, v)] := by
  cases r with
  | ok s v => simp only [GRes.lift, GRes.one, GRes.ok.injEq] at h; exact ⟨s, v, rfl, h.symm⟩
  | _ => simp [GRes.lift] at h

theorem ofOpt_ok {g : GSt} {v : Val} {o : Option St} {bs : List (GSt × Val)} (h : GRes.ofOpt g v o = .ok bs) :
    ∃ s, o = some s ∧ bs = [(g.withSt s, v)] := by
  cases o <;> simp_all [GRes.ofOpt, GRes.one]

end Guard.GRes

/-! ## The measure: strict subterms of a rigid entry value are smaller -/

def Val.sz : Val → Nat
  | .succ v => v.sz + 1
  | .pair a b => a.sz + b.sz + 1
  | .borrow _ v => v.sz + 1
  | .sealed _ a _ w => a.sz + w.sz + 1
  | _ => 1

/-- The shape of an entry value as refined so far: `S…S σ` or `S…S Z`. -/
def Val.Rigid : Val → Prop
  | .zero => True
  | .abs _ => True
  | .succ v => v.Rigid
  | _ => False

theorem VR.rigid_eq {θ : Nat → Val} : ∀ {v : Val}, v.Rigid → ∀ {w w' : Val}, VR θ v w → VR θ v w' → w = w'
  | .zero, _, _, _, h1, h2 => by simp only [VR] at h1 h2; rw [h1, h2]
  | .abs _, _, _, _, h1, h2 => by simp only [VR] at h1 h2; rw [h1, h2]
  | .succ v, hr, _, _, h1, h2 => by
    obtain ⟨a, rfl, ha⟩ := h1; obtain ⟨b, rfl, hb⟩ := h2
    rw [VR.rigid_eq (v := v) hr ha hb]

theorem VR.sz_lt {θ : Nat → Val} : ∀ {e : Val}, e.Rigid → ∀ {v w E : Val}, v.strictSub e = true →
    VR θ v w → VR θ e E → w.sz < E.sz
  | .succ e, hr, v, w, E, hs, hv, he => by
    have hr' : e.Rigid := hr
    obtain ⟨E', rfl, hE'⟩ := he
    simp only [Val.strictSub, Bool.or_eq_true, beq_iff_eq] at hs
    rcases hs with rfl | hs
    · rw [VR.rigid_eq hr' hv hE']; simp [Val.sz]
    · have := VR.sz_lt (e := e) hr' hs hv hE'; simp only [Val.sz]; omega
  | .zero, _, _, _, _, hs, _, _ => by simp [Val.strictSub] at hs
  | .abs _, _, _, _, _, hs, _, _ => by simp [Val.strictSub] at hs

/-! ## Extending and refining the instantiation -/

theorem VR.congr {θ θ' : Nat → Val} : ∀ {v w : Val}, (∀ a ∈ v.absIds, θ' a = θ a) → VR θ v w → VR θ' v w
  | .abs a, w, h, hv => by simp only [VR] at hv ⊢; rw [hv, h a (by simp [Val.absIds])]
  | .succ v, w, h, hv => by
    obtain ⟨w', rfl, hw'⟩ := hv
    exact ⟨w', rfl, VR.congr (fun a ha => h a (by simpa [Val.absIds] using ha)) hw'⟩
  | .pair a b, w, h, hv => by
    obtain ⟨c, d, rfl, h1, h2⟩ := hv
    exact ⟨c, d, rfl, VR.congr (fun x hx => h x (by simp [Val.absIds, hx])) h1,
      VR.congr (fun x hx => h x (by simp [Val.absIds, hx])) h2⟩
  | .zero, _, _, hv | .unit, _, _, hv | .star, _, _, hv | .moved, _, _, hv
  | .sealed .., _, _, hv | .borrow .., _, _, hv | .loan _, _, _, hv => hv

theorem FR.congr {θ θ' : Nat → Val} {F G : Frame} (h : ∀ a ∈ Frame.absIds F, θ' a = θ a) (hFG : FR θ F G) :
    FR θ' F G := by
  induction hFG with
  | nil => exact FR.nil
  | @cons x v w F G hvw _ ih =>
    simp only [Frame.absIds, List.flatMap_cons, List.mem_append] at h
    exact FR.cons (VR.congr (fun a ha => h a (Or.inl ha)) hvw) (ih fun a ha => h a (Or.inr ha))

theorem VR.substAbs {θ : Nat → Val} {a : Nat} {u : Val} (hu : VR θ u (θ a)) :
    ∀ {v w : Val}, VR θ v w → VR θ (Val.substAbs a u v) w
  | .abs b, w, hv => by
    simp only [VR] at hv; subst hv
    simp only [Val.substAbs]
    split
    · rename_i hb; subst hb; exact hu
    · simp [VR]
  | .succ v, w, hv => by
    obtain ⟨w', rfl, hw'⟩ := hv; exact ⟨w', rfl, VR.substAbs hu hw'⟩
  | .pair b c, w, hv => by
    obtain ⟨x, y, rfl, h1, h2⟩ := hv; exact ⟨x, y, rfl, VR.substAbs hu h1, VR.substAbs hu h2⟩
  | .zero, _, hv | .unit, _, hv | .star, _, hv | .moved, _, hv
  | .sealed .., _, hv | .borrow .., _, hv | .loan _, _, hv => by
    first | exact hv | (simp only [Val.substAbs]; trivial) | (simp [VR] at hv)

theorem FR.substAbs {θ : Nat → Val} {a : Nat} {u : Val} (hu : VR θ u (θ a)) {F G : Frame} (hFG : FR θ F G) :
    FR θ (F.mapVals (Val.substAbs a u)) G := by
  induction hFG with
  | nil => exact FR.nil
  | @cons x v w F G hvw _ ih => exact FR.cons (VR.substAbs hu hvw) ih

theorem VR.refineAll {θ : Nat → Val} : ∀ {rs : List (Nat × Val)}, (∀ r ∈ rs, VR θ r.2 (θ r.1)) →
    ∀ {v w : Val}, VR θ v w → VR θ (Val.refineAll rs v) w
  | [], _, _, _, hv => hv
  | r :: rs, h, v, w, hv => by
    simp only [Val.refineAll, List.foldl_cons]
    exact VR.refineAll (rs := rs) (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      (VR.substAbs (h r (by simp)) hv)

theorem Val.absIds_substAbs {a : Nat} {u : Val} : ∀ {v : Val} {b : Nat}, b ∈ (Val.substAbs a u v).absIds →
    b ∈ v.absIds ∨ b ∈ u.absIds
  | .abs c, b, h => by
    simp only [Val.substAbs] at h; split at h
    · exact Or.inr h
    · exact Or.inl h
  | .succ v, b, h => by simp only [Val.substAbs, Val.absIds] at h ⊢; exact Val.absIds_substAbs h
  | .pair x y, b, h => by
    simp only [Val.substAbs, Val.absIds, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases Val.absIds_substAbs h with h' | h' <;> simp [h']
    · rcases Val.absIds_substAbs h with h' | h' <;> simp [h']
  | .borrow _ v, b, h => by simp only [Val.substAbs, Val.absIds] at h ⊢; exact Val.absIds_substAbs h
  | .sealed _ x _ y, b, h => by
    simp only [Val.substAbs, Val.absIds, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases Val.absIds_substAbs h with h' | h' <;> simp [h']
    · rcases Val.absIds_substAbs h with h' | h' <;> simp [h']
  | .zero, _, h | .unit, _, h | .star, _, h | .moved, _, h | .loan _, _, h => by simp [Val.substAbs, Val.absIds] at h

theorem Val.nb_substAbs {a : Nat} {u : Val} (hu : u.nb = 0) : ∀ v : Val, (Val.substAbs a u v).nb = v.nb := by
  intro v
  induction v with
  | abs b => simp only [Val.substAbs]; split <;> simp [hu, Val.nb]
  | _ => simp_all [Val.substAbs, Val.nb]

theorem Frame.substAbs_bf {N : Nat} {a : Nat} {u : Val} (hu : BFVal N u) : ∀ {F : Frame},
    F.nb = 0 → (∀ b ∈ Frame.absIds F, b < N) →
    (F.mapVals (Val.substAbs a u)).nb = 0 ∧ ∀ b ∈ Frame.absIds (F.mapVals (Val.substAbs a u)), b < N
  | [], _, _ => by simp [Frame.mapVals, Frame.nb, Frame.absIds]
  | (x, v) :: F, h0, ha => by
    have hF := Frame.bf_cons.mp ⟨h0, ha⟩
    have ih := Frame.substAbs_bf (a := a) hu hF.2.1 hF.2.2
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    refine Frame.bf_cons.mpr ⟨⟨by rw [Val.nb_substAbs hu.1]; exact hF.1.1, fun b hb => ?_⟩, ih⟩
    rcases Val.absIds_substAbs hb with h | h
    · exact hF.1.2 b h
    · exact hu.2 b h

theorem Frame.nb_mapVals_substAbs {a : Nat} {u : Val} (hu : u.nb = 0) : ∀ F : Frame,
    (F.mapVals (Val.substAbs a u)).nb = F.nb
  | [] => rfl
  | (x, v) :: F => by
    have := Frame.nb_mapVals_substAbs (a := a) hu F
    simp only [Frame.mapVals, List.map_cons] at this ⊢
    simp only [Frame.nb, Val.nb_substAbs hu, this]

theorem Env.nb_mapVals_substAbs {a : Nat} {u : Val} (hu : u.nb = 0) : ∀ Ω : Env,
    (Ω.mapVals (Val.substAbs a u)).nb = Ω.nb
  | [] => rfl
  | F :: Ω => by
    have := Env.nb_mapVals_substAbs (a := a) hu Ω
    simp only [Env.mapVals, List.map_cons] at this ⊢
    simp only [Env.nb, Frame.nb_mapVals_substAbs hu, this]

theorem Val.rigid_substAbs {a : Nat} {u : Val} (hu : u.Rigid) : ∀ {v : Val}, v.Rigid → (Val.substAbs a u v).Rigid
  | .zero, _ => trivial
  | .abs b, _ => by
    simp only [Val.substAbs]; split
    · exact hu
    · exact trivial
  | .succ v, h => Val.rigid_substAbs (v := v) hu h

/-! ## The invariant between a checker branch and the actual run -/

/-- `g` (a checker branch) approximates the actual state with top frame `G` under `θ`: the top
frames correspond, both sides are borrow-free, the entry value as refined so far stands for the
actual entry value `E`, and the refinements made so far are true of `θ`. -/
structure GRel (θ : Nat → Val) (E : Val) (g : Guard.GSt) (G : Frame) (Ω' : Env) (N' : Nat) : Prop where
  top : ∃ F Ω, g.st.env = F :: Ω ∧ BFSt g.nabs F Ω ∧ FR θ F G
  conc : BFSt N' G Ω'
  entry : VR θ g.entry E
  rigid : g.entry.Rigid
  entryBelow : ∀ a ∈ g.entry.absIds, a < g.nabs
  refs : ∀ r ∈ g.refs, VR θ r.2 (θ r.1) ∧ r.1 < g.nabs ∧ ∀ a ∈ r.2.absIds, a < g.nabs

/-- What the actual result must satisfy after a checker run from `g` produced the branches `bs`. -/
def GPost (θ : Nat → Val) (E : Val) (g : Guard.GSt) (bs : List (Guard.GSt × Val)) (Ω' : Env) (N' k' : Nat) :
    Res → Prop
  | .ok c w => ∃ g' v θ' G', (g', v) ∈ bs ∧ c = ⟨G' :: Ω', k'⟩ ∧ GRel θ' E g' G' Ω' N' ∧ VR θ' v w ∧
      (∀ a < g.nabs, θ' a = θ a) ∧ g.nabs ≤ g'.nabs ∧ g.refs <+: g'.refs ∧ BFVal g'.nabs v ∧ BFVal N' w
  | .oof => False
  | _ => True

theorem GPost.ne_oof {θ : Nat → Val} {E : Val} {g : Guard.GSt} {bs : List (Guard.GSt × Val)} {Ω' : Env}
    {N' k' : Nat} {r : Res} (h : GPost θ E g bs Ω' N' k' r) : r ≠ .oof := by
  rintro rfl; exact h

theorem GPost.mono {θ : Nat → Val} {E : Val} {g : Guard.GSt} {bs bs' : List (Guard.GSt × Val)} {Ω' : Env}
    {N' k' : Nat} {r : Res} (hsub : ∀ x ∈ bs, x ∈ bs') (h : GPost θ E g bs Ω' N' k' r) :
    GPost θ E g bs' Ω' N' k' r := by
  cases r with
  | ok c w =>
    obtain ⟨g', v, θ', G', hmem, rest⟩ := h
    exact ⟨g', v, θ', G', hsub _ hmem, rest⟩
  | _ => exact h

/-- [Split], first arm: the actual scrutinee is `Z`. -/
theorem GRel.refineZ {θ : Nat → Val} {E : Val} {g : Guard.GSt} {G : Frame} {Ω' : Env} {N' : Nat}
    (h : GRel θ E g G Ω' N') {a : Nat} (ha : a < g.nabs) (hz : θ a = .zero) :
    GRel θ E (g.refine a .zero) G Ω' N' := by
  obtain ⟨F, Ω, he, hF, hFG⟩ := h.top
  have hu : VR θ .zero (θ a) := by simp [VR, hz]
  have hbz : BFVal g.nabs .zero := ⟨rfl, by simp [Val.absIds]⟩
  refine ⟨⟨F.mapVals (Val.substAbs a .zero), Env.mapVals (Val.substAbs a .zero) Ω, ?_, ?_, FR.substAbs hu hFG⟩,
    h.conc, VR.substAbs hu h.entry, Val.rigid_substAbs (show Val.Rigid .zero from trivial) h.rigid, ?_, ?_⟩
  · simp only [Guard.GSt.refine, he]; rfl
  · have := Frame.substAbs_bf (a := a) hbz hF.top hF.abs
    exact ⟨this.1, by rw [Env.nb_mapVals_substAbs rfl]; exact hF.rest, this.2⟩
  · intro b hb
    rcases Val.absIds_substAbs hb with h' | h'
    · exact h.entryBelow b h'
    · simp [Val.absIds] at h'
  · intro r hr
    simp only [Guard.GSt.refine, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h.refs r hr
    · exact ⟨hu, ha, by simp [Val.absIds]⟩

/-- [Split], second arm: the actual scrutinee is `S u`; the fresh predecessor `g.nabs` stands for
`u` in the extended instantiation `θ'`. -/
theorem GRel.refineS {θ θ' : Nat → Val} {E : Val} {g : Guard.GSt} {G : Frame} {Ω' : Env} {N' : Nat}
    (h : GRel θ E g G Ω' N') {a : Nat} (ha : a < g.nabs) {u : Val} (hs : θ a = .succ u)
    (hag : ∀ b < g.nabs, θ' b = θ b) (hθ' : θ' g.nabs = u) :
    GRel θ' E (({ g with nabs := g.nabs + 1 } : Guard.GSt).refine a (.succ (.abs g.nabs))) G Ω' N' := by
  obtain ⟨F, Ω, he, hF, hFG⟩ := h.top
  have hu : VR θ' (.succ (.abs g.nabs)) (θ' a) := by
    rw [hag a ha, hs]; exact ⟨u, rfl, hθ'.symm⟩
  have hbs : BFVal (g.nabs + 1) (.succ (.abs g.nabs)) := ⟨rfl, by simp [Val.absIds]⟩
  have hFG' : FR θ' F G := FR.congr (fun b hb => hag b (hF.abs b hb)) hFG
  refine ⟨⟨F.mapVals (Val.substAbs a (.succ (.abs g.nabs))), Env.mapVals (Val.substAbs a (.succ (.abs g.nabs))) Ω,
    ?_, ?_, FR.substAbs hu hFG'⟩, h.conc, VR.substAbs hu (VR.congr (fun b hb => hag b (h.entryBelow b hb)) h.entry),
    Val.rigid_substAbs (show Val.Rigid (.succ (.abs g.nabs)) from trivial) h.rigid, ?_, ?_⟩
  · simp only [Guard.GSt.refine, he]; rfl
  · have := Frame.substAbs_bf (a := a) hbs hF.top (fun b hb => Nat.lt_succ_of_lt (hF.abs b hb))
    exact ⟨this.1, by rw [Env.nb_mapVals_substAbs rfl]; exact hF.rest, this.2⟩
  · intro b hb
    simp only [Guard.GSt.refine] at hb ⊢
    rcases Val.absIds_substAbs hb with h' | h'
    · exact Nat.lt_succ_of_lt (h.entryBelow b h')
    · simp [Val.absIds] at h'; omega
  · intro r hr
    simp only [Guard.GSt.refine, List.mem_append, List.mem_singleton] at hr ⊢
    rcases hr with hr | rfl
    · obtain ⟨h1, h2, h3⟩ := h.refs r hr
      have h1' : VR θ' r.2 (θ r.1) := VR.congr (fun b hb => hag b (h3 b hb)) h1
      rw [← hag r.1 h2] at h1'
      exact ⟨h1', Nat.lt_succ_of_lt h2, fun b hb => Nat.lt_succ_of_lt (h3 b hb)⟩
    · exact ⟨hu, Nat.lt_succ_of_lt ha, by simp [Val.absIds]⟩

/-! ## Eventually-constant results -/

/-- `F` is eventually the constant `r`, and `Q r`. -/
def EvC (Q : Res → Prop) (F : Nat → Res) : Prop := ∃ n r, Q r ∧ ∀ m, n ≤ m → F m = r

theorem EvC.const {Q : Res → Prop} {r : Res} (h : Q r) : EvC Q (fun _ => r) := ⟨0, r, h, fun _ _ => rfl⟩

theorem EvC.of_eq {Q : Res → Prop} {F : Nat → Res} {r : Res} (h : ∀ n, F n = r) (hq : Q r) : EvC Q F :=
  ⟨0, r, hq, fun m _ => h m⟩

theorem EvC.mono {Q Q' : Res → Prop} {F : Nat → Res} (hQ : ∀ r, Q r → Q' r) (h : EvC Q F) : EvC Q' F := by
  obtain ⟨n, r, hr, hn⟩ := h; exact ⟨n, r, hQ r hr, hn⟩

theorem EvC.bind {Q₁ Q : Res → Prop} {F : Nat → Res} {G : Nat → St → Val → Res} (h : EvC Q₁ F)
    (hG : ∀ s v, Q₁ (.ok s v) → EvC Q (fun m => G m s v)) (hs : Q₁ .stuck → Q .stuck)
    (he : Q₁ .err → Q .err) (ho : Q₁ .oof → Q .oof) : EvC Q (fun m => (F m).bind (G m)) := by
  obtain ⟨n, r, hr, hn⟩ := h
  cases r with
  | ok s v =>
    obtain ⟨n', r', hr', hn'⟩ := hG s v hr
    refine ⟨max n n', r', hr', fun m hm => ?_⟩
    show (F m).bind (G m) = r'
    rw [hn m (by omega), Res.bind_ok]; exact hn' m (by omega)
  | stuck => exact ⟨n, .stuck, hs hr, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩
  | err => exact ⟨n, .err, he hr, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩
  | oof => exact ⟨n, .oof, ho hr, fun m hm => by show (F m).bind (G m) = _; rw [hn m hm]; rfl⟩

theorem EvC.execSucc {Q : Res → Prop} {P : Prog} {s : St} {t : Term}
    (h : EvC Q (fun m => exec P (m + 1) s t)) : EvC Q (fun m => exec P m s t) := by
  obtain ⟨n, r, hr, hn⟩ := h
  refine ⟨n + 1, r, hr, fun m hm => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact hn m' (by omega)

theorem EvC.callWith {Q : Res → Prop} {P : Prog} {cc : Bool} {h : String} {d : FunDef} {ws : List Val} {s : St}
    {n : Nat} (hn : callWith (exec P n) cc h d ws s ≠ .oof) (hq : Q (callWith (exec P n) cc h d ws s)) :
    EvC Q (fun m => callWith (exec P m) cc h d ws s) :=
  ⟨n, _, hq, fun _ hm => callWith_agree (fun _ _ ht => exec_mono_le P hm ht) cc h d ws s hn⟩

/-- Composing post-conditions: a post-condition from a later branch point is one from an earlier. -/
theorem GPost.trans {θ θ₁ : Nat → Val} {E : Val} {g g₁ : Guard.GSt} {bs cs : List (Guard.GSt × Val)}
    {Ω' : Env} {N' k' : Nat} (hag : ∀ a < g.nabs, θ₁ a = θ a) (hn : g.nabs ≤ g₁.nabs) (hr : g.refs <+: g₁.refs)
    (hsub : ∀ x ∈ cs, x ∈ bs) {r : Res} (h : GPost θ₁ E g₁ cs Ω' N' k' r) : GPost θ E g bs Ω' N' k' r := by
  cases r with
  | ok c w =>
    obtain ⟨g', v, θ', G', hmem, hc, hrel, hvw, hag', hn', hr', hbf, hbf'⟩ := h
    exact ⟨g', v, θ', G', hsub _ hmem, hc, hrel, hvw, fun a ha => by rw [hag' a (by omega), hag a ha],
      Nat.le_trans hn hn', hr.trans hr', hbf, hbf'⟩
  | _ => exact h

/-! ## Helpers for the simulation -/

theorem GRel.setTop {θ : Nat → Val} {E : Val} {g : Guard.GSt} {G : Frame} {Ω' : Env} {N' : Nat}
    (h : GRel θ E g G Ω' N') {F' G' : Frame} {Ω : Env} (hF' : BFSt g.nabs F' Ω) (hG' : BFSt N' G' Ω')
    (hFG' : FR θ F' G') (k : Nat) : GRel θ E (g.withSt ⟨F' :: Ω, k⟩) G' Ω' N' :=
  ⟨⟨F', Ω, rfl, hF', hFG'⟩, hG', h.entry, h.rigid, h.entryBelow, h.refs⟩

theorem GRel.st_eq {θ : Nat → Val} {E : Val} {g : Guard.GSt} {G : Frame} {Ω' : Env} {N' : Nat}
    (h : GRel θ E g G Ω' N') : ∃ F Ω, g.st = ⟨F :: Ω, g.st.next⟩ ∧ BFSt g.nabs F Ω ∧ FR θ F G := by
  obtain ⟨F, Ω, he, hF, hFG⟩ := h.top
  exact ⟨F, Ω, by cases hs : g.st; simp_all, hF, hFG⟩

theorem GSt.withSt_self (g : Guard.GSt) : g.withSt g.st = g := rfl

/-- The post-condition when the checker produced exactly this branch, with no new refinement. -/
theorem GPost.self {θ : Nat → Val} {E : Val} {g g' : Guard.GSt} {bs : List (Guard.GSt × Val)} {Ω' : Env}
    {N' k' : Nat} {G' : Frame} {v w : Val} (hrel : GRel θ E g' G' Ω' N') (hmem : (g', v) ∈ bs) (hvw : VR θ v w)
    (hn : g'.nabs = g.nabs) (hr : g'.refs = g.refs) (hv : BFVal g.nabs v) (hw : BFVal N' w) :
    GPost θ E g bs Ω' N' k' (.ok ⟨G' :: Ω', k'⟩ w) :=
  ⟨g', v, θ, G', hmem, rfl, hrel, hvw, fun _ _ => rfl, by omega, by rw [hr]; exact List.prefix_refl _,
    by rw [hn]; exact hv, hw⟩

theorem assignTail_sim {θ : Nat → Val} {N N' : Nat} {F G : Frame} {Ω Ω' : Env} {k k' : Nat}
    (hF : BFSt N F Ω) (hG : BFSt N' G Ω') (hFG : FR θ F G) {p : Place} {v w : Val} (hv : BFVal N v)
    (hw : BFVal N' w) (hvw : VR θ v w) {s₁ : St} {u : Val} (h : Guard.assignTail p v ⟨F :: Ω, k⟩ = .ok s₁ u) :
    ∃ F₁, s₁ = ⟨F₁ :: Ω, k⟩ ∧ u = .unit ∧ BFSt N F₁ Ω ∧
      (Guard.assignTail p w ⟨G :: Ω', k'⟩ = .err ∨
        ∃ G₁, Guard.assignTail p w ⟨G :: Ω', k'⟩ = .ok ⟨G₁ :: Ω', k'⟩ .unit ∧ BFSt N' G₁ Ω' ∧ FR θ F₁ G₁) := by
  unfold Guard.assignTail at h ⊢
  cases ha : access true p.root p.path ⟨F :: Ω, k⟩ with
  | ok s3 c =>
    rw [ha, Res.bind_ok] at h
    obtain ⟨rfl, hc⟩ := access_bf hF ha
    obtain ⟨c', ha', hcc⟩ := access_sim (k' := k') hF hG hFG ha
    obtain ⟨-, hc'⟩ := access_bf hG ha'
    rw [ha', Res.bind_ok]
    rw [if_neg (fun hh => hh.2 hv.1)] at h
    rw [if_neg (fun hh => hh.2 hw.1)]
    split at h
    · cases h
    · rename_i s4 hs4
      obtain ⟨F4, G4, rfl, hs4', hFG4⟩ := setPlace_sim (Ω' := Ω') (k' := k') hFG hvw hs4
      obtain ⟨F4', he4, hF4⟩ := setPlace_bf hF hv hs4
      simp only [St.mk.injEq, List.cons.injEq] at he4; obtain ⟨⟨rfl, -⟩, -⟩ := he4
      obtain ⟨G4', he4', hG4⟩ := setPlace_bf hG hw hs4'
      simp only [St.mk.injEq, List.cons.injEq] at he4'; obtain ⟨⟨rfl, -⟩, -⟩ := he4'
      rw [dropVal_bf hF4.env_nb rfl hc.1] at h
      simp only [Res.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨F4, rfl, rfl, hF4, Or.inr ⟨G4, ?_, hG4, hFG4⟩⟩
      rw [hs4']; dsimp only
      rw [dropVal_bf hG4.env_nb rfl hc'.1]
  | _ => rw [ha] at h; cases h

/-! ## The simulation -/

/-- The standing hypotheses on the recursive definition `f` (declared `by x_j`) whose body is
simulated, at actual entry value `E`: the fragment, and the induction hypothesis on the entry
value (a call to `f` at a strictly smaller decreasing argument terminates). -/
structure RecHyps (P : Prog) (f : String) (d : FunDef) (j : Nat) (E : Val) : Prop where
  bf : P.BF
  find : P.find f = some d
  ih : ∀ ws', (∃ w, ws'[j]? = some w ∧ w.sz < E.sz) → CallTermBF P f ws'

/-- The simulation at checker fuel `n`: a passing checker run from `g` covers the actual run. -/
def SimG (P : Prog) (f : String) (j : Nat) (E : Val) (n : Nat) : Prop :=
  ∀ (g : Guard.GSt) (t : Term) (bs : List (Guard.GSt × Val)) (θ : Nat → Val) (G : Frame) (Ω' : Env)
    (N' k' : Nat), t.noBorrow = true → (∀ h ∈ t.calls, h ≠ f → ∀ ws, CallTermBF P h ws) →
    Guard.gexec P f j n g t = .ok bs → GRel θ E g G Ω' N' →
    EvC (GPost θ E g bs Ω' N' k') (fun m => exec P m ⟨G :: Ω', k'⟩ t)

/-- A term the checker runs as one machine step. -/
theorem sim_step {P : Prog} (hP : P.BF) {E : Val} {g : Guard.GSt} {t : Term} {bs : List (Guard.GSt × Val)}
    {θ : Nat → Val} {G : Frame} {Ω' : Env} {N' k' : Nat} (ht : t.noBorrow = true)
    (hno : exec P 1 ⟨G :: Ω', k'⟩ t ≠ .oof) (h : Guard.GRes.lift g (exec P 1 g.st t) = .ok bs)
    (hrel : GRel θ E g G Ω' N') : GPost θ E g bs Ω' N' k' (exec P 1 ⟨G :: Ω', k'⟩ t) := by
  obtain ⟨s, v, h1, rfl⟩ := Guard.GRes.lift_ok h
  obtain ⟨F, Ω, hs, hF, hFG⟩ := hrel.st_eq
  rw [hs] at h1
  obtain ⟨F₁, rfl, hF₁, hv⟩ := exec_bf hP 1 g.nabs F Ω _ t s v ht hF h1
  have hsim := sim_exec hP θ 1 g.nabs N' F G Ω Ω' _ k' t F₁ v ht hF hrel.conc hFG h1
  cases hr : exec P 1 ⟨G :: Ω', k'⟩ t with
  | ok c w =>
    rw [hr] at hsim
    obtain ⟨G₁, rfl, hFG₁, hvw⟩ := hsim
    obtain ⟨G₁', he, hG₁, hw⟩ := exec_bf hP 1 N' G Ω' k' t _ w ht hrel.conc hr
    simp only [St.mk.injEq, List.cons.injEq] at he; obtain ⟨⟨rfl, -⟩, -⟩ := he
    exact GPost.self (hrel.setTop hF₁ hG₁ hFG₁ g.st.next) (by simp) hvw rfl rfl hv hw
  | stuck => rw [hr] at hsim; exact hsim.elim
  | err => trivial
  | oof => exact absurd hr hno

theorem letTail_sim {θ : Nat → Val} {N N' : Nat} {F G : Frame} {Ω Ω' : Env} {k k' : Nat}
    (hF : BFSt N F Ω) (hG : BFSt N' G Ω') (hFG : FR θ F G) {x : Var} {v w : Val} (hv : BFVal N v)
    (hw : BFVal N' w) {s₁ : St} (h : Guard.letTail x v ⟨F :: Ω, k⟩ = some s₁) :
    ∃ F₁ G₁, s₁ = ⟨F₁ :: Ω, k⟩ ∧ BFSt N F₁ Ω ∧ BFSt N' G₁ Ω' ∧ FR θ F₁ G₁ ∧
      (match St.unbind x ⟨G :: Ω', k'⟩ with
        | none => Res.err
        | some (c, s) => match dropVal w c s with
          | none => .err
          | some s => .ok s w) = .ok ⟨G₁ :: Ω', k'⟩ w := by
  unfold Guard.letTail at h
  split at h
  · cases h
  · rename_i c s hu
    simp only [St.unbind] at hu
    obtain ⟨⟨c0, F₁⟩, hr, he⟩ := Option.map_eq_some_iff.mp hu
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hc, hF₁0, hF₁a⟩ := Frame.remove_bf hF.top hF.abs hr
    have hF₁ : BFSt N F₁ Ω := ⟨hF₁0, hF.rest, hF₁a⟩
    obtain ⟨c', G₁, hr', _, hFG₁⟩ := hFG.remove hr
    have hu' : St.unbind x ⟨G :: Ω', k'⟩ = some (c', ⟨G₁ :: Ω', k'⟩) := by simp [St.unbind, hr']
    obtain ⟨G₁', he', hG₁, hc'⟩ := unbind_bf hG hu'
    simp only [St.mk.injEq, List.cons.injEq] at he'; obtain ⟨⟨rfl, -⟩, -⟩ := he'
    rw [dropVal_bf hF₁.env_nb hv.1 hc.1] at h
    simp only [Option.some.injEq] at h; subst h
    refine ⟨F₁, G₁, rfl, hF₁, hG₁, hFG₁, ?_⟩
    rw [hu']; dsimp only
    rw [dropVal_bf hG₁.env_nb hw.1 hc'.1]

theorem Val.absIds_refineAll {N : Nat} : ∀ {rs : List (Nat × Val)}, (∀ r ∈ rs, ∀ a ∈ r.2.absIds, a < N) →
    ∀ {v : Val}, (∀ a ∈ v.absIds, a < N) → ∀ a ∈ (Val.refineAll rs v).absIds, a < N
  | [], _, _, hv => hv
  | r :: rs, h, v, hv => by
    simp only [Val.refineAll, List.foldl_cons]
    refine Val.absIds_refineAll (rs := rs) (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) (fun a ha => ?_)
    rcases Val.absIds_substAbs ha with h' | h'
    · exact hv a h'
    · exact h r (by simp) a h'

theorem guardArgs_none {d : FunDef} {j : Nat} {e : Val} {ws : List Val} (h : Guard.guardArgs d j e ws = none) :
    ∃ p w, d.params[j]? = some p ∧ ws[j]? = some w ∧ (Guard.recContent p.2 w).strictSub e = true := by
  unfold Guard.guardArgs at h
  split at h
  · rename_i x ty w h1 h2
    simp only at h
    split at h
    · exact ⟨(x, ty), w, h1, h2, by assumption⟩
    · cases h
  · cases h

theorem recContent_noref {ty : Ty} (h : ty.isRef = false) (w : Val) : Guard.recContent ty w = w := by
  cases ty <;> simp_all [Ty.isRef, Guard.recContent]

theorem VRs.get {θ : Nat → Val} : ∀ {ws ws' : List Val}, VRs θ ws ws' → ∀ {j : Nat} {w : Val}, ws[j]? = some w →
    ∃ w', ws'[j]? = some w' ∧ VR θ w w'
  | [], [], VRs.nil, j, w, h => by simp at h
  | _ :: _, _ :: _, VRs.cons hvw hs, 0, w, h => by simp at h; subst h; exact ⟨_, rfl, hvw⟩
  | _ :: _, _ :: _, VRs.cons _ hs, j + 1, w, h => by simpa using VRs.get hs (j := j) (by simpa using h)

theorem closeRes_bf {f : String} {ws : List Val} {N : Nat} (hws : ∀ w ∈ ws, BFVal N w) {v : Val}
    (h : v = .unit ∨ ∃ k, v = .sealed f (Val.ofList ws) k .unit) : BFVal N v := by
  rcases h with rfl | ⟨k, rfl⟩
  · exact ⟨rfl, by simp [Val.absIds]⟩
  · refine ⟨by simp [Val.nb, Val.nb_ofList (fun w hw => (hws w hw).1)], fun a ha => ?_⟩
    simp only [Val.absIds, List.mem_append] at ha
    rcases ha with ha | ha
    · obtain ⟨w, hw, ha⟩ := Val.absIds_ofList ha; exact (hws w hw).2 a ha
    · simp at ha

theorem exec_one_read_ne_oof {P : Prog} {c : St} {p : Place} : exec P 1 c (.read p) ≠ .oof := by
  simp only [exec]
  refine Res.bind_ne_oof (access_ne_oof' _ _ _ _) fun s c => ?_
  split
  · simp
  · split <;> simp
  · simp

theorem sim_gexecArgs {P : Prog} {f : String} {j : Nat} {E : Val} (hP : P.BF) {n : Nat}
    (ih : SimG P f j E n) : ∀ (args : List Term) (i : Nat) (g : Guard.GSt) (bs : List (Guard.GSt × Val))
    (θ : Nat → Val) (G : Frame) (Ω' : Env) (N' k' : Nat), (∀ a ∈ args, a.noBorrow = true) →
    (∀ a ∈ args, ∀ x ∈ a.calls, x ≠ f → ∀ ws, CallTermBF P x ws) →
    Guard.gexecArgs (Guard.gexec P f j n) i g args = .ok bs → GRel θ E g G Ω' N' →
    EvC (GPost θ E g bs Ω' N' k') (fun m => execArgs (exec P m) i ⟨G :: Ω', k'⟩ args)
  | [], i, g, bs, θ, G, Ω', N', k', _, _, h, hrel => by
    simp only [Guard.gexecArgs, Guard.GRes.one, Guard.GRes.ok.injEq] at h; subst h
    exact EvC.of_eq (r := .ok ⟨G :: Ω', k'⟩ .unit) (fun _ => rfl)
      (GPost.self (v := .unit) hrel (by simp) trivial rfl rfl ⟨rfl, by simp [Val.absIds]⟩
        ⟨rfl, by simp [Val.absIds]⟩)
  | a :: as, i, g, bs, θ, G, Ω', N', k', hb, hc, h, hrel => by
    simp only [Guard.gexecArgs] at h
    simp only [execArgs]
    obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
    refine EvC.bind (ih g a bs₁ θ G Ω' N' k' (hb a (by simp)) (hc a (by simp)) h1 hrel)
      (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
    obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, hvw, hag, hn, hr, hv₁, hw₁⟩ := hpost
    obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
    obtain ⟨F₁, Ω₁, hs₁, hF₁, hFG₁⟩ := hrel₁.st_eq
    simp only at hk1
    have hb' : g₁.st.bind (.tmp i) v₁ = ⟨((.tmp i, v₁) :: F₁) :: Ω₁, g₁.st.next⟩ := by rw [hs₁]; rfl
    rw [hb'] at hk1
    have hrel₂ := hrel₁.setTop (hF₁.cons (x := .tmp i) hv₁) (hrel₁.conc.cons (x := .tmp i) hw₁)
      (FR.cons hvw hFG₁) g₁.st.next
    have hsim := sim_gexecArgs hP ih as (i + 1) _ cs θ₁ _ Ω' N' k' (fun b hb' => hb b (List.mem_cons_of_mem _ hb'))
      (fun b hb' => hc b (List.mem_cons_of_mem _ hb')) hk1 hrel₂
    exact hsim.mono fun r hq =>
      GPost.trans (g := g) (g₁ := g₁.withSt ⟨((.tmp i, v₁) :: F₁) :: Ω₁, g₁.st.next⟩) hag hn hr hsub hq

theorem sim_gexec {P : Prog} {f : String} {d : FunDef} {j : Nat} {E : Val} (hy : RecHyps P f d j E) :
    ∀ n, SimG P f j E n := by
  intro n
  induction n with
  | zero => intro g t bs θ G Ω' N' k' _ _ h; simp [Guard.gexec] at h
  | succ n ih =>
    intro g t bs θ G Ω' N' k' ht hc h hrel
    apply EvC.execSucc
    cases t with
    | read p =>
      simp only [Guard.gexec] at h
      exact EvC.of_eq (fun m => rfl) (sim_step hy.bf ht exec_one_read_ne_oof h hrel)
    | borrow p => simp [Term.noBorrow] at ht
    | zero =>
      simp only [Guard.gexec] at h
      exact EvC.of_eq (fun m => rfl) (sim_step hy.bf ht (by simp [exec]) h hrel)
    | unit =>
      simp only [Guard.gexec] at h
      exact EvC.of_eq (fun m => rfl) (sim_step hy.bf ht (by simp [exec]) h hrel)
    | erase t =>
      simp only [Guard.gexec] at h
      split at h
      · cases h
      · simp only [Guard.GRes.one, Guard.GRes.ok.injEq] at h; subst h
        exact EvC.of_eq (r := .ok ⟨G :: Ω', k'⟩ .star) (fun m => rfl)
          (GPost.self (v := .star) hrel (by simp) trivial rfl rfl ⟨rfl, by simp [Val.absIds]⟩
            ⟨rfl, by simp [Val.absIds]⟩)
    | assign p t =>
      simp only [Guard.gexec] at h
      show EvC _ (fun m => (exec P m ⟨G :: Ω', k'⟩ t).bind fun s v => Guard.assignTail p v s)
      simp only [Term.noBorrow] at ht
      obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
      refine EvC.bind (ih g t bs₁ θ G Ω' N' k' ht (fun x hx => hc x (by simp [Term.calls, hx])) h1 hrel)
        (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, hvw, hag, hn, hr, hv₁, hw₁⟩ := hpost
      obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
      obtain ⟨F₁, Ω₁, hs₁, hF₁, hFG₁⟩ := hrel₁.st_eq
      obtain ⟨s₂, u₂, hat, rfl⟩ := Guard.GRes.lift_ok hk1
      rw [hs₁] at hat
      obtain ⟨F₂, rfl, rfl, hF₂, hc'⟩ := assignTail_sim (k' := k') hF₁ hrel₁.conc hFG₁ hv₁ hw₁ hvw hat
      rcases hc' with hc' | ⟨G₂, hc', hG₂, hFG₂⟩
      · exact EvC.of_eq (fun _ => hc') trivial
      · refine EvC.of_eq (fun _ => hc') (GPost.trans hag hn hr hsub ?_)
        exact GPost.self (v := .unit) (hrel₁.setTop hF₂ hG₂ hFG₂ g₁.st.next) (by simp) trivial rfl rfl
          ⟨rfl, by simp [Val.absIds]⟩ ⟨rfl, by simp [Val.absIds]⟩
    | letIn x t u =>
      simp only [Guard.gexec] at h
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
      refine EvC.bind (ih g t bs₁ θ G Ω' N' k' ht.1 (fun x hx => hc x (by simp [Term.calls, hx])) h1 hrel)
        (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, hvw, hag, hn, hr, hv₁, hw₁⟩ := hpost
      obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
      obtain ⟨F₁, Ω₁, hs₁, hF₁, hFG₁⟩ := hrel₁.st_eq
      simp only at hk1
      obtain ⟨bs₂, h2, hk2⟩ := Guard.GRes.bind_ok hk1
      have hb : g₁.st.bind x v₁ = ⟨((x, v₁) :: F₁) :: Ω₁, g₁.st.next⟩ := by rw [hs₁]; rfl
      rw [hb] at h2
      have hrel₂ := hrel₁.setTop (hF₁.cons (x := x) hv₁) (hrel₁.conc.cons (x := x) hw₁) (FR.cons hvw hFG₁) g₁.st.next
      refine EvC.bind (ih _ u bs₂ θ₁ _ Ω' N' k' ht.2 (fun y hy => hc y (by simp [Term.calls, hy])) h2 hrel₂)
        (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₂, v₂, θ₂, G₂, hmem₂, rfl, hrel₂', hvw₂, hag₂, hn₂, hr₂, hv₂, hw₂⟩ := hpost
      obtain ⟨cs₂, hk3, hsub₂⟩ := hk2 (g₂, v₂) hmem₂
      obtain ⟨s₃, hl, rfl⟩ := Guard.GRes.ofOpt_ok hk3
      obtain ⟨F₂, Ω₂, hs₂, hF₂, hFG₂⟩ := hrel₂'.st_eq
      rw [hs₂] at hl
      obtain ⟨F₃, G₃, rfl, hF₃, hG₃, hFG₃, hc'⟩ := letTail_sim (k' := k') hF₂ hrel₂'.conc hFG₂ hv₂ hw₂ hl
      refine EvC.of_eq (fun _ => hc') ?_
      refine GPost.trans (g₁ := g₁.withSt ⟨((x, v₁) :: F₁) :: Ω₁, g₁.st.next⟩) hag hn hr hsub
        (GPost.trans hag₂ hn₂ hr₂ hsub₂ ?_)
      exact GPost.self (hrel₂'.setTop hF₃ hG₃ hFG₃ g₂.st.next) (by simp) hvw₂ rfl rfl hv₂ hw₂
    | seq t u =>
      simp only [Guard.gexec] at h
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
      refine EvC.bind (ih g t bs₁ θ G Ω' N' k' ht.1 (fun x hx => hc x (by simp [Term.calls, hx])) h1 hrel)
        (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, _, hag, hn, hr, hv₁, hw₁⟩ := hpost
      obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
      obtain ⟨F₁, Ω₁, hs₁, hF₁, _⟩ := hrel₁.st_eq
      have hd : dropVal .unit v₁ g₁.st = some g₁.st := by rw [hs₁]; exact dropVal_bf hF₁.env_nb rfl hv₁.1
      simp only [hd, GSt.withSt_self] at hk1
      simp only [dropVal_bf (extra := .unit) (s := ⟨G₁ :: Ω', k'⟩) hrel₁.conc.env_nb rfl hw₁.1]
      exact (ih g₁ u cs θ₁ G₁ Ω' N' k' ht.2 (fun x hx => hc x (by simp [Term.calls, hx])) hk1 hrel₁).mono
        fun r hq => GPost.trans hag hn hr hsub hq
    | succ t =>
      simp only [Guard.gexec] at h
      simp only [exec]
      simp only [Term.noBorrow] at ht
      obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
      refine EvC.bind (ih g t bs₁ θ G Ω' N' k' ht (fun x hx => hc x (by simp [Term.calls, hx])) h1 hrel)
        (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, hvw, hag, hn, hr, hv₁, hw₁⟩ := hpost
      obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
      simp only at hk1
      rw [if_pos hv₁.1] at hk1
      simp only [Guard.GRes.one, Guard.GRes.ok.injEq] at hk1; subst hk1
      refine EvC.of_eq (r := .ok ⟨G₁ :: Ω', k'⟩ (.succ w)) (fun m => by simp [hw₁.1]) ?_
      refine GPost.trans hag hn hr hsub (GPost.self (v := .succ v₁) hrel₁ (by simp) ⟨w, rfl, hvw⟩ rfl rfl ?_ ?_)
      · exact ⟨by simp [Val.nb, hv₁.1], by simpa [Val.absIds] using hv₁.2⟩
      · exact ⟨by simp [Val.nb, hw₁.1], by simpa [Val.absIds] using hw₁.2⟩
    | pair t u =>
      simp only [Guard.gexec] at h
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
      refine EvC.bind (ih g t bs₁ θ G Ω' N' k' ht.1 (fun x hx => hc x (by simp [Term.calls, hx])) h1 hrel)
        (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, hvw, hag, hn, hr, hv₁, hw₁⟩ := hpost
      obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
      simp only at hk1
      obtain ⟨bs₂, h2, hk2⟩ := Guard.GRes.bind_ok hk1
      refine EvC.bind (ih g₁ u bs₂ θ₁ G₁ Ω' N' k' ht.2 (fun y hy => hc y (by simp [Term.calls, hy])) h2 hrel₁)
        (fun c w₂ hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
      obtain ⟨g₂, v₂, θ₂, G₂, hmem₂, rfl, hrel₂, hvw₂, hag₂, hn₂, hr₂, hv₂, hw₂⟩ := hpost
      obtain ⟨cs₂, hk3, hsub₂⟩ := hk2 (g₂, v₂) hmem₂
      simp only at hk3
      split at hk3
      · rename_i hnb
        simp only [Guard.GRes.one, Guard.GRes.ok.injEq] at hk3; subst hk3
        refine EvC.of_eq (r := .ok ⟨G₂ :: Ω', k'⟩ (.pair w w₂)) (fun m => by simp [hw₁.1, hw₂.1]) ?_
        refine GPost.trans hag hn hr hsub (GPost.trans hag₂ hn₂ hr₂ hsub₂ ?_)
        have hnew : ∀ r ∈ g₂.refs.drop g₁.refs.length, r ∈ g₂.refs := fun r hr' => List.mem_of_mem_drop hr'
        refine GPost.self (v := .pair (Val.refineAll (List.drop g₁.refs.length g₂.refs) v₁) v₂) hrel₂ (by simp)
          ⟨w, w₂, rfl, ?_, hvw₂⟩ rfl rfl ⟨?_, ?_⟩ ⟨?_, ?_⟩
        · refine VR.refineAll (fun r hr' => (hrel₂.refs r (hnew r hr')).1) ?_
          exact VR.congr (fun a ha => hag₂ a (hv₁.2 a ha)) hvw
        · simp [Val.nb, hnb.1, hnb.2]
        · intro a ha
          simp only [Val.absIds, List.mem_append] at ha
          rcases ha with ha | ha
          · exact Val.absIds_refineAll (fun r hr' => (hrel₂.refs r (hnew r hr')).2.2)
              (fun b hb => Nat.lt_of_lt_of_le (hv₁.2 b hb) hn₂) a ha
          · exact hv₂.2 a ha
        · simp [Val.nb, hw₁.1, hw₂.1]
        · intro a ha
          simp only [Val.absIds, List.mem_append] at ha
          exact ha.elim (hw₁.2 a) (hw₂.2 a)
      · cases hk3
    | mtch p tz y ts =>
      simp only [Guard.gexec] at h
      simp only [exec]
      simp only [Term.noBorrow, Bool.and_eq_true] at ht
      have hcz : ∀ x ∈ tz.calls, x ≠ f → ∀ ws, CallTermBF P x ws := fun x hx => hc x (by simp [Term.calls, hx])
      have hcs : ∀ x ∈ (ts.substVar y p.fst).calls, x ≠ f → ∀ ws, CallTermBF P x ws := fun x hx =>
        hc x (by simp only [Term.calls_substVar] at hx; simp [Term.calls, hx])
      have hts : (ts.substVar y p.fst).noBorrow = true := by rw [Term.noBorrow_substVar]; exact ht.2
      obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
      obtain ⟨s₀, c₀, ha, rfl⟩ := Guard.GRes.lift_ok h1
      obtain ⟨cs, hk1, hsub⟩ := hk _ (List.mem_singleton_self _)
      obtain ⟨F, Ω, hs, hF, hFG⟩ := hrel.st_eq
      rw [hs] at ha
      obtain ⟨rfl, hc₀⟩ := access_bf hF ha
      obtain ⟨c', ha', hcc⟩ := access_sim (k' := k') hF hrel.conc hFG ha
      simp only [ha', Res.bind_ok]
      rw [← hs, GSt.withSt_self] at hk1
      simp only at hk1
      cases c₀ with
      | zero =>
        simp only [VR] at hcc; subst hcc
        exact (ih g tz cs θ G Ω' N' k' ht.1 hcz hk1 hrel).mono fun r hq => GPost.mono hsub hq
      | succ v₀ =>
        obtain ⟨w₀, rfl, _⟩ := hcc
        exact (ih g _ cs θ G Ω' N' k' hts hcs hk1 hrel).mono fun r hq => GPost.mono hsub hq
      | abs a =>
        simp only [VR] at hcc; subst hcc
        have ha' : a < g.nabs := hc₀.2 a (by simp [Val.absIds])
        obtain ⟨xs, ys, hz, hsu, rfl⟩ := Guard.GRes.app_ok hk1
        cases hθ : θ a with
        | zero =>
          have hsim := ih _ tz xs θ G Ω' N' k' ht.1 hcz hz (hrel.refineZ ha' hθ)
          refine EvC.mono (fun r hq => ?_) hsim
          exact GPost.trans (g := g) (g₁ := g.refine a .zero) (θ₁ := θ) (fun _ _ => rfl) (Nat.le_refl g.nabs)
            (List.prefix_append g.refs _) (fun x hx => hsub x (List.mem_append_left _ hx)) hq
        | succ u =>
          have hsim := ih _ _ ys (fun b => if b = g.nabs then u else θ b) G Ω' N' k' hts hcs hsu
            (hrel.refineS ha' hθ (fun b hb => by simp [Nat.ne_of_lt hb]) (by simp))
          refine EvC.mono (fun r hq => ?_) hsim
          exact GPost.trans (g := g) (g₁ := ({ g with nabs := g.nabs + 1 } : Guard.GSt).refine a (.succ (.abs g.nabs)))
            (fun b hb => by simp [Nat.ne_of_lt hb]) (Nat.le_succ g.nabs) (List.prefix_append g.refs _)
            (fun x hx => hsub x (List.mem_append_right _ hx)) hq
        | _ => first
          | exact EvC.of_eq (r := .stuck) (fun _ => rfl) trivial
          | exact EvC.of_eq (r := .err) (fun _ => rfl) trivial
      | _ => simp at hk1
    | call fn args cc =>
      simp only [Guard.gexec] at h
      simp only [exec]
      cases hf : P.find fn with
      | none => rw [hf] at h; cases h
      | some d' =>
        rw [hf] at h; simp only at h ⊢
        by_cases hp : d'.ret = .prop
        · simp only [hp, if_true] at h ⊢
          split at h
          · cases h
          · simp only [Guard.GRes.one, Guard.GRes.ok.injEq] at h; subst h
            exact EvC.of_eq (r := .ok ⟨G :: Ω', k'⟩ .star) (fun _ => rfl)
              (GPost.self (v := .star) hrel (by simp) trivial rfl rfl ⟨rfl, by simp [Val.absIds]⟩
                ⟨rfl, by simp [Val.absIds]⟩)
        · simp only [hp, if_false] at h ⊢
          have hbl := Term.noBorrowList_iff.mp (by simpa [Term.noBorrow] using ht)
          have hca : ∀ a ∈ args, ∀ x ∈ a.calls, x ≠ f → ∀ ws, CallTermBF P x ws := fun a ha x hx =>
            hc x (by simp only [Term.calls, List.mem_cons, Term.mem_callsList]; exact Or.inr ⟨a, ha, hx⟩)
          obtain ⟨bs₁, h1, hk⟩ := Guard.GRes.bind_ok h
          refine EvC.bind (sim_gexecArgs hy.bf ih args 0 g bs₁ θ G Ω' N' k' hbl hca h1 hrel)
            (fun c w hpost => ?_) (fun _ => trivial) (fun _ => trivial) (fun h => h.elim)
          obtain ⟨g₁, v₁, θ₁, G₁, hmem, rfl, hrel₁, _, hag, hn, hr, _, _⟩ := hpost
          obtain ⟨cs, hk1, hsub⟩ := hk (g₁, v₁) hmem
          obtain ⟨F₁, Ω₁, hs₁, hF₁, hFG₁⟩ := hrel₁.st_eq
          simp only at hk1
          split at hk1
          · cases hk1
          · rename_i ws s₂ htt
            rw [hs₁] at htt
            obtain ⟨F₂, G₂, ws', rfl, htt', hvs, hFG₂⟩ := takeTemps_sim (Ω' := Ω') (k' := k') _ hFG₁ htt
            obtain ⟨F₂', he2, hF₂, hws⟩ := takeTemps_bf _ F₁ ws _ hF₁ htt
            simp only [St.mk.injEq, List.cons.injEq] at he2; obtain ⟨⟨rfl, -⟩, -⟩ := he2
            obtain ⟨G₂', he2', hG₂, hws'⟩ := takeTemps_bf _ G₁ ws' _ hrel₁.conc htt'
            simp only [St.mk.injEq, List.cons.injEq] at he2'; obtain ⟨⟨rfl, -⟩, -⟩ := he2'
            simp only [htt']
            have hrel₂ := hrel₁.setTop hF₂ hG₂ hFG₂ g₁.st.next
            by_cases hff : fn = f
            · subst hff
              rw [hy.find] at hf; cases hf
              simp only [if_true] at hk1
              split at hk1
              · cases hk1
              · rename_i hguard
                obtain ⟨s₃, v₃, hcl, rfl⟩ := Guard.GRes.lift_ok hk1
                obtain ⟨rfl, hv₃⟩ := closeCall_bf (hy.bf _ _ hy.find) hcl
                obtain ⟨⟨x, ty⟩, w, hpj, hwj, hsub'⟩ := guardArgs_none hguard
                have hty : ty.isRef = false := (hy.bf _ _ hy.find).params (x, ty) (List.mem_of_getElem? hpj)
                rw [recContent_noref hty] at hsub'
                obtain ⟨w', hwj', hww'⟩ := hvs.get hwj
                have hlt : w'.sz < E.sz := VR.sz_lt hrel₁.rigid hsub' hww' hrel₁.entry
                obtain ⟨m₀, hm₀⟩ := hy.ih ws' ⟨w', hwj', hlt⟩ d hy.find cc N' G₂ Ω' k' hG₂ hws'
                refine EvC.callWith hm₀ ?_
                cases hr₀ : callWith (exec P m₀) cc fn d ws' ⟨G₂ :: Ω', k'⟩ with
                | ok c'' w'' =>
                  obtain ⟨rfl, hw''⟩ := callWith_bf (exec_bf hy.bf m₀) (hy.bf _ _ hy.find) hG₂ hws' hr₀
                  exact GPost.trans hag hn hr hsub (GPost.self hrel₂ (List.mem_singleton.mpr rfl) (VR.wild hv₃ w'') rfl rfl
                    (closeRes_bf hws hv₃) hw'')
                | stuck => trivial
                | err => trivial
                | oof => exact absurd hr₀ hm₀
            · simp only [hff, if_false] at hk1
              obtain ⟨s₃, v₃, hcw, rfl⟩ := Guard.GRes.lift_ok hk1
              obtain ⟨m₀, hm₀⟩ := hc fn (by simp [Term.calls]) hff ws' d' hf cc N' G₂ Ω' k' hG₂ hws'
              let M := max n m₀
              have hcw' : callWith (exec P n) cc fn d' ws ⟨F₂ :: Ω₁, g₁.st.next⟩ = .ok s₃ v₃ := hcw
              have hsymM : callWith (exec P M) cc fn d' ws ⟨F₂ :: Ω₁, g₁.st.next⟩ = .ok s₃ v₃ := by
                rw [callWith_agree (fun _ _ ht => exec_mono_le P (Nat.le_max_left n m₀) ht) cc fn d' ws _
                  (by rw [hcw']; simp)]
                exact hcw'
              have hconM : callWith (exec P M) cc fn d' ws' ⟨G₂ :: Ω', k'⟩ =
                  callWith (exec P m₀) cc fn d' ws' ⟨G₂ :: Ω', k'⟩ :=
                callWith_agree (fun _ _ ht => exec_mono_le P (Nat.le_max_right n m₀) ht) cc fn d' ws' _ hm₀
              obtain ⟨rfl, hsim⟩ := sim_callWith (sim_exec hy.bf θ₁ M) (exec_bf hy.bf M) (hy.bf _ _ hf) hF₂ hG₂
                hFG₂ hws hws' hvs hsymM
              obtain ⟨-, hv₃⟩ := callWith_bf (exec_bf hy.bf n) (hy.bf _ _ hf) hF₂ hws hcw'
              refine EvC.callWith (n := M) (by rw [hconM]; exact hm₀) ?_
              cases hr₀ : callWith (exec P M) cc fn d' ws' ⟨G₂ :: Ω', k'⟩ with
              | ok c'' w'' =>
                rw [hr₀] at hsim
                obtain ⟨G₃, rfl, hFG₃, hvw₃⟩ := hsim
                obtain ⟨he3, hw''⟩ := callWith_bf (exec_bf hy.bf M) (hy.bf _ _ hf) hG₂ hws' hr₀
                simp only [St.mk.injEq, List.cons.injEq] at he3; obtain ⟨⟨rfl, -⟩, -⟩ := he3
                exact GPost.trans hag hn hr hsub (GPost.self hrel₂ (List.mem_singleton.mpr rfl) hvw₃ rfl rfl hv₃ hw'')
              | stuck => trivial
              | err => trivial
              | oof => rw [hconM] at hr₀; exact absurd hr₀ hm₀

end OchrMeta
