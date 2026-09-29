import OchrMeta.GuardSimG

/-! # Lemma 1 (termination) for borrow-free programs

`termination_bf`: in a well-guarded borrow-free program, every run of a borrow-free term from a
borrow-free state terminates (concrete or symbolic, in a value, an error, or a stuck state).

The proof: induction on the call order (`termination_of_calls_bf'`); for a recursive definition
`f` (declared `by x_j`), strong induction on the size of the actual entry value `E` of the
decreasing argument (`callTermBF_rec`).  The checker ran `f`'s body from the generic call state
(`Guard.genG`), which approximates the actual call state under `θ₀ : σᵢ ↦ wsᵢ`
(`GRel.generic`); the simulation `sim_gexec` then gives termination of the actual body run,
using the induction hypothesis at each recursive call (whose decreasing argument the guard found
strictly below the entry value) and the call order at every other call. -/

namespace OchrMeta
open Guard

/-! ## The generic call state approximates every actual call -/

theorem genArgs_length : ∀ (i : Nat) (ps : List (Var × Ty)), (Guard.genArgs i ps).length = ps.length
  | _, [] => rfl
  | i, (_, .ref _) :: ps => by simp [Guard.genArgs, genArgs_length (i + 1) ps]
  | i, (_, .nat) :: ps | i, (_, .unit) :: ps | i, (_, .pair _ _) :: ps | i, (_, .prop) :: ps => by
    simp [Guard.genArgs, genArgs_length (i + 1) ps]

theorem genArgs_vrs {θ : Nat → Val} : ∀ (i : Nat) (ps : List (Var × Ty)) (ws : List Val),
    (∀ p ∈ ps, p.2.isRef = false) → ws.length = ps.length →
    (∀ k (hk : k < ws.length), θ (i + k) = ws[k]) → VRs θ (Guard.genArgs i ps) ws
  | _, [], [], _, _, _ => VRs.nil
  | _, [], _ :: _, _, h, _ => by simp at h
  | _, _ :: _, [], _, h, _ => by simp at h
  | i, (x, ty) :: ps, w :: ws, hp, hl, hθ => by
    have hr : ty.isRef = false := hp (x, ty) (by simp)
    have rest := genArgs_vrs (θ := θ) (i + 1) ps ws (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
      (by simpa using hl) (fun k hk => by rw [show i + 1 + k = i + (k + 1) by omega]; exact hθ (k + 1) (by simp; omega))
    have h0 : VR θ (.abs i) w := by simp only [VR]; exact (hθ 0 (by simp)).symm
    cases ty with
    | ref _ => simp [Ty.isRef] at hr
    | _ => simp only [Guard.genArgs]; exact VRs.cons h0 rest

theorem genArgs_bf : ∀ (i : Nat) (ps : List (Var × Ty)), (∀ p ∈ ps, p.2.isRef = false) →
    ∀ w ∈ Guard.genArgs i ps, BFVal (i + ps.length) w ∧ w.borrows = []
  | _, [], _, w, hw => by simp [Guard.genArgs] at hw
  | i, (x, ty) :: ps, hp, w, hw => by
    have hr : ty.isRef = false := hp (x, ty) (by simp)
    have rest := genArgs_bf (i + 1) ps (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
    cases ty with
    | ref _ => simp [Ty.isRef] at hr
    | _ =>
      simp only [Guard.genArgs, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨⟨rfl, by simp [Val.absIds]⟩, rfl⟩
      · obtain ⟨⟨h1, h2⟩, h3⟩ := rest w hw
        exact ⟨⟨h1, fun a ha => by have := h2 a ha; simp; omega⟩, h3⟩

theorem Frame.borrows_zip_nil : ∀ (xs : List Var) (ws : List Val), (∀ w ∈ ws, w.borrows = []) →
    Frame.borrows (xs.zip ws) = []
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, w :: ws, h => by
    simp only [List.zip_cons_cons, Frame.borrows, h w (by simp), List.nil_append]
    exact Frame.borrows_zip_nil xs ws (fun v hv => h v (by simp [hv]))

theorem portsOf_nil_of {F : Frame} (h : Frame.borrows F = []) : Env.portsOf [F] = [] := by
  simp [Env.portsOf, Env.portKeys, Env.borrows, h]

/-- The generic call state of a borrow-free recursive definition approximates the actual call
state at arguments `ws`, under `θ₀ : σᵢ ↦ wsᵢ`, with actual entry value `ws[j]`. -/
theorem GRel.generic {d : FunDef} (hd : d.BF) {j : Nat} (hj : j < d.params.length) {ws : List Val}
    (hlen : ws.length = d.params.length) {N : Nat} (hws : ∀ w ∈ ws, BFVal N w) {F : Frame} {Ω : Env}
    (hs : BFSt N F Ω) :
    GRel (fun a => ws.getD a .unit) (ws[j]'(by omega)) (Guard.genG d j) (paramFrame d ws) (F :: Ω) N := by
  have hga := genArgs_bf 0 d.params hd.params
  have hF0 := paramFrame_bf (N := 0 + d.params.length) d (d.params.map Prod.fst) (Guard.genArgs 0 d.params)
    (fun w hw => (hga w hw).1)
  have hports : Env.portsOf [paramFrame d (Guard.genArgs 0 d.params)] = [] :=
    portsOf_nil_of (Frame.borrows_zip_nil _ _ (fun w hw => (hga w hw).2))
  have hvrs : VRs (fun a => ws.getD a .unit) (Guard.genArgs 0 d.params) ws :=
    genArgs_vrs 0 d.params ws hd.params hlen (fun k hk => by simp [List.getD_eq_getElem?_getD, hk])
  have hp := paramFrame_bf (N := N) d (d.params.map Prod.fst) ws hws
  refine ⟨⟨paramFrame d (Guard.genArgs 0 d.params), [Env.portsOf [paramFrame d (Guard.genArgs 0 d.params)]],
    rfl, ⟨?_, ?_, ?_⟩, paramFrame_sim _ hvrs⟩, ⟨hp.1, hs.env_nb, hp.2⟩, ?_, trivial, ?_, by simp [Guard.genG]⟩
  · exact hF0.1
  · rw [hports]; rfl
  · intro a ha; have := hF0.2 a ha; simpa [Guard.genG] using this
  · simp [Guard.genG, VR, List.getD_eq_getElem?_getD, show j < ws.length by omega]
  · simp [Guard.genG, Val.absIds, hj]

/-! ## Recursive definitions: induction on the entry value -/

/-- A well-guarded borrow-free recursive definition terminates at every argument tuple, from
every borrow-free call point, given that the other functions its body calls do. -/
theorem callTermBF_rec {P : Prog} (hP : P.BF) {f : String} {d : FunDef} {b : Term} {j : Nat}
    (hd : P.find f = some d) (hb : d.body = some b) (hj : d.recPos = some j) {fuel : Nat}
    (hacc : Guard.checkDef P f fuel = .accept)
    (hother : ∀ h ∈ b.calls, h ≠ f → ∀ ws, CallTermBF P h ws) : ∀ ws, CallTermBF P f ws := by
  have hdbf := hP f d hd
  unfold Guard.checkDef at hacc
  rw [hd] at hacc; simp only [hb, hj] at hacc
  split at hacc
  · rename_i hjlt
    split at hacc
    · cases hacc
    · rename_i bs hg
      have key : ∀ K ws, (ws[j]?.map Val.sz).getD 0 < K → CallTermBF P f ws := by
        intro K
        induction K with
        | zero => intro ws h; omega
        | succ K ih =>
          intro ws hK d' hd' cc N F Ω k hs hws
          rw [hd] at hd'; cases hd'
          by_cases hlen : ws.length = d.params.length
          · have hjw : j < ws.length := by omega
            have hy : RecHyps P f d j (ws[j]'hjw) := ⟨hP, hd, fun ws' ⟨w, hw, hlt⟩ => ih ws' (by
              simp only [hw, Option.map_some, Option.getD_some]
              simp only [List.getElem?_eq_getElem hjw, Option.map_some, Option.getD_some] at hK
              omega)⟩
            obtain ⟨n, r, hq, hn⟩ := sim_gexec hy fuel (Guard.genG d j) b bs (fun a => ws.getD a .unit)
              (paramFrame d ws) (F :: Ω) N k (hdbf.body b hb) hother hg (GRel.generic hdbf hjlt hlen hws hs)
            refine ⟨n, callWith_ne_oof (fun b' hb' => ?_)⟩
            rw [hb] at hb'; cases hb'
            have := hn n (Nat.le_refl n)
            simp only at this
            rw [show St.push (paramFrame d ws) ⟨F :: Ω, k⟩ = ⟨paramFrame d ws :: F :: Ω, k⟩ from rfl, this]
            exact hq.ne_oof
          · exact ⟨0, by unfold callWith; rw [hb]; simp [hlen]⟩
      intro ws
      exact key _ ws (Nat.lt_succ_self _)
  · cases hacc

/-! ## The call order, with the recursive step -/

theorem termination_of_calls_bf' {P : Prog} (hord : Guard.Ordered P) (hP : P.BF)
    (hstep : ∀ h d b, P.find h = some d → d.body = some b → d.recPos.isSome = true →
      (∀ g ∈ b.calls, g ≠ h → ∀ ws, CallTermBF P g ws) → ∀ ws, CallTermBF P h ws) :
    ∀ h ws, CallTermBF P h ws := by
  have key : ∀ n (A : Prog) f d B, A.length < n → P = A ++ (f, d) :: B → ∀ ws, CallTermBF P f ws := by
    intro n
    induction n with
    | zero => intro A f d B h; omega
    | succ n ih =>
      intro A f d B hlen hPe ws
      obtain ⟨_, hfA, hcalls⟩ := orderedAux_split A [] f d B (by rw [← hPe]; exact hord)
      have hd : P.find f = some d := by rw [hPe]; exact lookup_append_of_not_mem hfA
      have hearlier : ∀ b, d.body = some b → ∀ g ∈ b.calls, g ≠ f → ∀ ws', CallTermBF P g ws' := by
        intro b hb g hg hgf ws'
        rcases hcalls b hb g hg with h1 | h1 | h1
        · simp at h1
        · obtain ⟨⟨g', dg⟩, hmem, rfl⟩ := List.mem_map.mp h1
          obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hmem
          exact ih A₁ g' dg (A₂ ++ (f, d) :: B) (by simp at hlen; omega) (by rw [hPe]; simp) ws'
        · exact absurd h1.1 hgf
      cases hbd : d.body with
      | none => exact callTermBF_of_body hd (fun b hb => by simp [hbd] at hb) ws
      | some b =>
        cases hr : d.recPos with
        | some j => exact hstep f d b hd hbd (by simp [hr]) (hearlier b hbd) ws
        | none =>
          refine callTermBF_of_body hd (fun b' hb' N F Ω k hs => ?_) ws
          rw [hbd] at hb'; cases hb'
          exact exec_total_bf hP (b.sz + 1) b (by omega) ((hP f d hd).body b hbd)
            (fun g hg ws' => by
              rcases hcalls b hbd g hg with h1 | h1 | h1
              · simp at h1
              · exact hearlier b hbd g hg (fun hgf => by subst hgf; exact hfA h1) ws'
              · simp [hr] at h1) N F Ω k hs
  intro h ws d hd
  obtain ⟨A, B, hPe, _⟩ := List.lookup_eq_some_iff.mp hd
  exact key (A.length + 1) A h d B (by omega) hPe ws d hd

/-! ## Lemma 1 -/

theorem Nat.lt_foldr_max_succ : ∀ {l : List Nat} {a : Nat}, a ∈ l → a < l.foldr max 0 + 1
  | [], _, h => by simp at h
  | b :: l, a, h => by
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · omega
    · have := Nat.lt_foldr_max_succ h; omega

/-- **Lemma 1 (termination) for the borrow-free fragment.**  In a well-guarded program with no
`&p` term and no `&T` parameter or result, every run of a borrow-free term from a state with no
borrow terminates: in a value, an error, or a stuck state. -/
theorem termination_bf {P : Prog} (hP : Guard.WellGuarded P) (hbf : P.BF) (t : Term)
    (ht : t.noBorrow = true) {F : Frame} {Ω : Env} {k : Nat} (hs : Env.nb (F :: Ω) = 0) :
    ∃ n, exec P n ⟨F :: Ω, k⟩ t ≠ .oof := by
  have hs' : BFSt ((Frame.absIds F).foldr max 0 + 1) F Ω := by
    simp only [Env.nb] at hs
    exact ⟨by omega, by omega, fun a ha => Nat.lt_foldr_max_succ ha⟩
  refine exec_total_bf hbf (t.sz + 1) t (by omega) ht (fun h _ ws => ?_) _ F Ω k hs'
  refine termination_of_calls_bf' hP.1 hbf (fun h d b hd hb hrec hcalls ws => ?_) h ws
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hrec
  obtain ⟨fuel, hacc⟩ := hP.2 h d hd hrec
  exact callTermBF_rec hbf hd hb hj hacc hcalls ws

end OchrMeta
