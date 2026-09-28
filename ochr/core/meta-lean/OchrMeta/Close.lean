import OchrMeta.Rename
import OchrMeta.Interp

/-! # The [Close] equations: sealed programs are the call's backward functions

A sealed program produced by [Close] at a call `f(w̄)` is re-run by [Seal] as the closed program
`L; C; K` from the empty environment.  Its head call `C` is the same call on renamed loans, at a
different counter; this file relates the two runs.  Part A: the isolated call run commutes with
renaming loans. -/

namespace OchrMeta

section
variable {ρ : Nat → Nat}

theorem Val.borrows_rename (v : Val) : (v.rename ρ).borrows = v.borrows.map ρ := by
  induction v <;> simp_all [Val.rename, Val.borrows]

theorem Frame.borrows_rename (F : Frame) : Frame.borrows (F.mapVals (Val.rename ρ)) = F.borrows.map ρ := by
  induction F with
  | nil => rfl
  | cons b F ih =>
    obtain ⟨x, v⟩ := b
    simp only [Frame.mapVals, List.map_cons] at ih ⊢
    simp [Frame.borrows, ih, Val.borrows_rename]

theorem Env.borrows_rename (Ω : Env) : (Ω.rename ρ).borrows = Ω.borrows.map ρ := by
  induction Ω with
  | nil => rfl
  | cons F Ω ih =>
    simp only [Env.rename, Env.mapVals, List.map_cons] at ih ⊢
    simp [Env.borrows, ih, Frame.borrows_rename]

theorem zipIdx_map_fst {α β : Type} (g : α → β) : ∀ (L : List α) (n : Nat),
    (L.map g).zipIdx n = (L.zipIdx n).map fun p => (g p.1, p.2) := by
  intro L
  induction L with
  | nil => intro n; rfl
  | cons a L ih => intro n; simp [List.zipIdx_cons, ih]

theorem Env.portsOf_rename (Ω : Env) :
    Env.portsOf (Ω.rename ρ) = (Env.portsOf Ω).mapVals (Val.rename ρ) := by
  simp only [Env.portsOf, Env.portKeys, Env.borrows_rename, zipIdx_map_fst, List.map_map, Frame.mapVals]
  rfl

theorem genEnv_rename (d : FunDef) (ws : List Val) (N δ : Nat) :
    (⟨[paramFrame d (ws.map (Val.rename ρ)), Env.portsOf [paramFrame d (ws.map (Val.rename ρ))]], N + δ⟩ : St) =
      St.rename ρ δ ⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], N⟩ := by
  have h1 := paramFrame_rename (ρ := ρ) d ws
  have h2 : ([Frame.mapVals (Val.rename ρ) (paramFrame d ws)] : Env) = Env.rename ρ [paramFrame d ws] := rfl
  simp only [St.rename, h1, h2, Env.portsOf_rename]
  rfl

/-- The isolated call run commutes with renaming loans. -/
theorem callRun_rename (Pr : Prog) (n : Nat) (d : FunDef) (b : Term) (ws : List Val) {N δ : Nat}
    (hρ : Function.Injective ρ) (hc : CC ρ δ N) :
    callRun Pr n d b (ws.map (Val.rename ρ)) (N + δ) = (callRun Pr n d b ws N).rename ρ δ := by
  unfold callRun
  rw [genEnv_rename]
  have e := exec_rename Pr ρ hρ δ n ⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], N⟩ b hc
  simp only at e
  rw [show St.rename ρ δ ⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], N⟩ =
      ⟨Env.rename ρ [paramFrame d ws, Env.portsOf [paramFrame d ws]], N + δ⟩ from rfl, e]
  cases exec Pr n ⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], N⟩ b with
  | ok s v =>
    simp only [Res.rename_ok, Res.bind_ok]
    rw [popFrame_rename hρ]
    cases popFrame v s <;> rfl
  | _ => rfl

end
end OchrMeta

/-! ## Part B: a renaming that relabels a list of names and shifts the rest -/

namespace OchrMeta

/-- `src[j] ↦ base + j`; other names `≥ N` shift by `δ`; the rest stay. -/
def relabel (src : List Nat) (base N δ : Nat) (l : Nat) : Nat :=
  match src.idxOf? l with
  | some j => base + j
  | none => if N ≤ l then l + δ else l

theorem relabel_inj {src : List Nat} {base N δ : Nat} (hbase : N ≤ base)
    (htop : base + src.length ≤ N + δ) : Function.Injective (relabel src base N δ) := by
  intro a b h
  unfold relabel at h
  cases ha : src.idxOf? a with
  | some j =>
    obtain ⟨hj, hja, _⟩ := List.idxOf?_eq_some_iff.mp ha
    rw [ha] at h
    cases hb : src.idxOf? b with
    | some j' =>
      obtain ⟨hj', hjb, _⟩ := List.idxOf?_eq_some_iff.mp hb
      rw [hb] at h
      simp only at h
      have : j = j' := by omega
      subst this; rw [← hja, ← hjb]
    | none =>
      rw [hb] at h
      simp only at h
      split at h <;> omega
  | none =>
    rw [ha] at h
    cases hb : src.idxOf? b with
    | some j' =>
      obtain ⟨hj', _, _⟩ := List.idxOf?_eq_some_iff.mp hb
      rw [hb] at h
      simp only at h
      split at h <;> omega
    | none =>
      rw [hb] at h
      simp only at h
      split at h <;> split at h <;> omega

theorem relabel_cc {src : List Nat} {base N δ : Nat} (hsrc : ∀ l ∈ src, l < N) :
    CC (relabel src base N δ) δ N := by
  intro l hl
  have : l ∉ src := fun h => by have := hsrc l h; omega
  simp [relabel, List.idxOf?_eq_none_iff.mpr this, hl]

theorem relabel_src {src : List Nat} (hnd : src.Nodup) {base N δ : Nat} (j : Nat) (hj : j < src.length) :
    relabel src base N δ src[j] = base + j := by
  have : src.idxOf? src[j] = some j := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨hj, rfl, fun j' hj' heq => ?_⟩
    have := (List.getElem_inj hnd).mp heq
    omega
  simp [relabel, this]

end OchrMeta

/-! ## Part C: what the sealed program's argument evaluation produces -/

namespace OchrMeta

/-- The arguments the sealed program's head call receives: fresh borrows `c, c+1, …` of the
cells `cᵢ` at borrow positions, the values themselves elsewhere. -/
def sealWs : Nat → List Ty → List Val → List Val
  | c, .ref _ :: tys, a :: as => .borrow c a :: sealWs (c + 1) tys as
  | c, _ :: tys, a :: as => a :: sealWs c tys as
  | _, _, _ => []

def nRefs : List Ty → Nat
  | [] => 0
  | .ref _ :: tys => nRefs tys + 1
  | _ :: tys => nRefs tys

/-- The cells `cᵢ` after the arguments: borrowed cells hold their loans. -/
def argFrameAfter : Nat → Nat → List Ty → List Val → Frame
  | i, c, .ref _ :: tys, _ :: as => (Var.arg i, .loan c) :: argFrameAfter (i + 1) (c + 1) tys as
  | i, c, _ :: tys, a :: as => (Var.arg i, a) :: argFrameAfter (i + 1) c tys as
  | _, _, _, _ => []

/-- Argument temporaries, most recent first. -/
def tempFrame (vs : List Val) : Frame := (vs.zipIdx.map fun p => (Var.tmp p.2, p.1)).reverse

theorem tempFrame_snoc (vs : List Val) (v : Val) :
    tempFrame (vs ++ [v]) = (Var.tmp vs.length, v) :: tempFrame vs := by
  simp [tempFrame, List.zipIdx_append]

theorem Val.firstLive_noloans {f : Nat → Bool} : ∀ {v : Val}, v.loans = [] → v.firstLive f = none := by
  intro v hv
  induction v with
  | loan m => simp [Val.loans] at hv
  | _ => simp_all [Val.firstLive, Val.loans]

/-- A value with no loans at all is not affected by [Access]. -/
theorem walk_noloans {f : Nat → Bool} {deep : Bool} {v : Val} (hv : v.loans = []) : walk f deep v [] = .done v := by
  have hh : headLoan f v = none := by cases v <;> simp_all [headLoan, Val.loans]
  simp [walk, hh, Val.firstLive_noloans hv]

end OchrMeta

namespace OchrMeta

theorem lookup_append_of_not {A B : Frame} {x : Var} (h : ∀ b ∈ A, b.1 ≠ x) :
    (A ++ B).lookup x = B.lookup x := by
  induction A with
  | nil => rfl
  | cons b A ih =>
    obtain ⟨y, v⟩ := b
    have hy : y ≠ x := h (y, v) (by simp)
    have : (x == y) = false := by simp [Ne.symm hy]
    simp [List.lookup_cons, this, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem set_append_of_not {A B : Frame} {x : Var} {v : Val} (h : ∀ b ∈ A, b.1 ≠ x) :
    Frame.set x v (A ++ B) = A ++ Frame.set x v B := by
  induction A with
  | nil => rfl
  | cons b A ih =>
    obtain ⟨y, w⟩ := b
    have hy : y ≠ x := h (y, w) (by simp)
    simp [Frame.set, hy, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem remove_append_of_not {A B : Frame} {x : Var} (h : ∀ b ∈ A, b.1 ≠ x) :
    Frame.remove x (A ++ B) = (Frame.remove x B).map fun p => (p.1, A ++ p.2) := by
  induction A with
  | nil => simp
  | cons b A ih =>
    obtain ⟨y, w⟩ := b
    have hy : y ≠ x := h (y, w) (by simp)
    simp only [List.cons_append, Frame.remove, hy, if_false, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      Option.map_map]
    rfl

/-- One borrowed argument of the sealed program's head call. -/
theorem exec_borrow_cell (Pr : Prog) (k : Nat) {F : Frame} {c : Nat} {x : Var} {a : Val}
    (hl : F.lookup x = some a) (ha : a.loans = []) (hm : a ≠ .moved) (hnb : a.nb = 0) :
    exec Pr (k + 1) ⟨[F], c⟩ (.borrow (.var x)) = .ok ⟨[Frame.set x (.loan c) F], c + 1⟩ (.borrow c a) := by
  have hacc : access true x [] ⟨[F], c⟩ = .ok ⟨[F], c⟩ a := by
    rw [access]
    simp only [St.lookup, List.head?_cons, Option.bind_some, hl, walk_noloans ha]
  simp only [exec, Place.root, Place.path, hacc, Res.bind_ok]
  have hc : ¬ (a = .moved ∨ a.nb ≠ 0) := by simp [hm, hnb]
  rw [if_neg hc]
  simp [St.setPlace, St.lookup, hl, Val.set, St.setVar, St.modTop]

/-- One copied argument of the sealed program's head call. -/
theorem exec_read_cell (Pr : Prog) (k : Nat) {F : Frame} {c : Nat} {x : Var} {a : Val}
    (hl : F.lookup x = some a) (ha : a.loans = []) (hm : a ≠ .moved) (hnb : a.nb = 0) :
    exec Pr (k + 1) ⟨[F], c⟩ (.read (.var x)) = .ok ⟨[F], c⟩ a := by
  have hacc : access true x [] ⟨[F], c⟩ = .ok ⟨[F], c⟩ a := by
    rw [access]
    simp only [St.lookup, List.head?_cons, Option.bind_some, hl, walk_noloans ha]
  simp only [exec, Place.root, Place.path, hacc, Res.bind_ok]
  cases a with
  | moved => exact absurd rfl hm
  | borrow l w => simp [Val.nb] at hnb
  | _ => rfl

end OchrMeta

namespace OchrMeta

theorem tempFrame_keys (vs : List Val) : ∀ b ∈ tempFrame vs, ∃ j, b.1 = Var.tmp j := by
  intro b hb
  simp only [tempFrame, List.mem_reverse, List.mem_map] at hb
  obtain ⟨p, _, rfl⟩ := hb
  exact ⟨p.2, rfl⟩

theorem lookup_argFrame_head (i : Nat) (a : Val) (as : List Val) (tail : Frame) :
    (argFrame i (a :: as) ++ tail).lookup (Var.arg i) = some a := by
  simp [argFrame, List.lookup_cons]

theorem set_argFrame_head (i : Nat) (a v : Val) (as : List Val) (tail : Frame) :
    Frame.set (Var.arg i) v (argFrame i (a :: as) ++ tail) = (Var.arg i, v) :: (argFrame (i + 1) as ++ tail) := by
  simp [argFrame, Frame.set]

/-- The sealed program's argument evaluation, exactly. -/
theorem execArgs_cells (Pr : Prog) (k : Nat) (tail : Frame) :
    ∀ (tys : List Ty) (as : List Val) (i c : Nat) (done : List Val) (A : Frame),
      tys.length = as.length → done.length = i →
      (∀ a ∈ as, a.loans = [] ∧ a ≠ .moved ∧ a.nb = 0) →
      (∀ b ∈ A, ∃ j < i, b.1 = Var.arg j) →
      execArgs (exec Pr (k + 1)) i ⟨[tempFrame done ++ A ++ (argFrame i as ++ tail)], c⟩ (sealArgTerms i tys) =
        .ok ⟨[tempFrame (done ++ sealWs c tys as) ++ A ++ (argFrameAfter i c tys as ++ tail)], c + nRefs tys⟩ .unit := by
  intro tys
  induction tys with
  | nil =>
    intro as i c done A hlen _ _ _
    cases as with
    | cons a as => simp at hlen
    | nil => simp [sealArgTerms, execArgs, sealWs, argFrameAfter, argFrame, nRefs]
  | cons ty tys ih =>
    intro as i c done A hlen hd has hA
    cases as with
    | nil => simp at hlen
    | cons a as =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      obtain ⟨ha1, ha2, ha3⟩ := has a (by simp)
      have has' : ∀ a ∈ as, a.loans = [] ∧ a ≠ .moved ∧ a.nb = 0 := fun a h => has a (List.mem_cons_of_mem _ h)
      have hnot : ∀ b ∈ tempFrame done ++ A, b.1 ≠ Var.arg i := by
        intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · obtain ⟨j, hj⟩ := tempFrame_keys done b hb; rw [hj]; simp
        · obtain ⟨j, hj, hbj⟩ := hA b hb; rw [hbj]; simp; omega
      have hl : (tempFrame done ++ A ++ (argFrame i (a :: as) ++ tail)).lookup (Var.arg i) = some a := by
        rw [lookup_append_of_not hnot, lookup_argFrame_head]
      have hA' : ∀ (v : Val), ∀ b ∈ A ++ [(Var.arg i, v)], ∃ j < i + 1, b.1 = Var.arg j := by
        intro v b hb
        rcases List.mem_append.mp hb with hb | hb
        · obtain ⟨j, hj, hbj⟩ := hA b hb; exact ⟨j, by omega, hbj⟩
        · simp at hb; subst hb; exact ⟨i, by omega, rfl⟩
      have hd' : ∀ v : Val, (done ++ [v]).length = i + 1 := by intro v; simp [hd]
      cases ty with
      | ref T =>
        simp only [sealArgTerms, execArgs]
        rw [exec_borrow_cell Pr k hl ha1 ha2 ha3, Res.bind_ok]
        rw [set_append_of_not hnot, set_argFrame_head]
        have e : St.bind (Var.tmp i) (.borrow c a)
            ⟨[tempFrame done ++ A ++ ((Var.arg i, Val.loan c) :: (argFrame (i + 1) as ++ tail))], c + 1⟩ =
            ⟨[tempFrame (done ++ [.borrow c a]) ++ (A ++ [(Var.arg i, .loan c)]) ++ (argFrame (i + 1) as ++ tail)], c + 1⟩ := by
          simp [St.bind, St.modTop, tempFrame_snoc, hd]
        rw [e, ih as (i + 1) (c + 1) _ _ hlen (hd' _) has' (hA' _)]
        simp [sealWs, argFrameAfter, nRefs, Nat.add_assoc, Nat.add_comm 1]
      | _ =>
        simp only [sealArgTerms, execArgs]
        rw [exec_read_cell Pr k hl ha1 ha2 ha3, Res.bind_ok]
        have e : ∀ tl : Frame, St.bind (Var.tmp i) a ⟨[tempFrame done ++ A ++ ((Var.arg i, a) :: tl)], c⟩ =
            ⟨[tempFrame (done ++ [a]) ++ (A ++ [(Var.arg i, a)]) ++ tl], c⟩ := by
          intro tl; simp [St.bind, St.modTop, tempFrame_snoc, hd]
        simp only [argFrame, List.cons_append] at e ⊢
        rw [e, ih as (i + 1) c _ _ hlen (hd' _) has' (hA' _)]
        simp [sealWs, argFrameAfter, nRefs]

end OchrMeta

namespace OchrMeta

def tempFrameFrom (vs : List Val) (i : Nat) : Frame := ((vs.zipIdx i).map fun p => (Var.tmp p.2, p.1)).reverse

theorem tempFrameFrom_cons (v : Val) (vs : List Val) (i : Nat) :
    tempFrameFrom (v :: vs) i = tempFrameFrom vs (i + 1) ++ [(Var.tmp i, v)] := by
  simp [tempFrameFrom, List.zipIdx_cons]

theorem tempFrameFrom_keys (vs : List Val) (i : Nat) : ∀ b ∈ tempFrameFrom vs i, ∃ j, i ≤ j ∧ b.1 = Var.tmp j := by
  intro b hb
  simp only [tempFrameFrom, List.mem_reverse, List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  exact ⟨p.2, (List.mem_zipIdx hp).1, rfl⟩

theorem takeTemps_tempFrameFrom (c : Nat) (G : Frame) (hG : ∀ b ∈ G, ∀ j, b.1 ≠ Var.tmp j) :
    ∀ (vs : List Val) (i : Nat), takeTemps (List.range' i vs.length) ⟨[tempFrameFrom vs i ++ G], c⟩ =
      some (vs, ⟨[G], c⟩) := by
  intro vs
  induction vs with
  | nil => intro i; simp [tempFrameFrom, takeTemps]
  | cons v vs ih =>
    intro i
    simp only [List.length_cons, List.range'_succ, takeTemps]
    have hnot : ∀ b ∈ tempFrameFrom vs (i + 1), b.1 ≠ Var.tmp i := by
      intro b hb
      obtain ⟨j, hj, hbj⟩ := tempFrameFrom_keys vs (i + 1) b hb
      rw [hbj]; simp; omega
    have hu : St.unbind (Var.tmp i) ⟨[tempFrameFrom (v :: vs) i ++ G], c⟩ =
        some (v, ⟨[tempFrameFrom vs (i + 1) ++ G], c⟩) := by
      simp only [St.unbind, tempFrameFrom_cons, List.append_assoc, List.singleton_append]
      rw [remove_append_of_not hnot]
      simp [Frame.remove]
    rw [hu]
    simp only [Option.bind_some]
    rw [ih (i + 1)]
    rfl

theorem tempFrame_eq_from (vs : List Val) : tempFrame vs = tempFrameFrom vs 0 := rfl

theorem sealArgTerms_length : ∀ (i : Nat) (tys : List Ty), (sealArgTerms i tys).length = tys.length := by
  intro i tys
  induction tys generalizing i with
  | nil => rfl
  | cons ty tys ih => cases ty <;> simp [sealArgTerms, ih]

theorem sealWs_length : ∀ (c : Nat) (tys : List Ty) (as : List Val), tys.length = as.length →
    (sealWs c tys as).length = tys.length := by
  intro c tys
  induction tys generalizing c with
  | nil => intro as _; simp [sealWs]
  | cons ty tys ih =>
    intro as h
    cases as with
    | nil => simp at h
    | cons a as => cases ty <;> simp_all [sealWs]

theorem argFrameAfter_keys : ∀ (i c : Nat) (tys : List Ty) (as : List Val),
    ∀ b ∈ argFrameAfter i c tys as, ∃ j, b.1 = Var.arg j := by
  intro i c tys
  induction tys generalizing i c with
  | nil => intro as b hb; simp [argFrameAfter] at hb
  | cons ty tys ih =>
    intro as b hb
    cases as with
    | nil => cases ty <;> simp [argFrameAfter] at hb
    | cons a as =>
      cases ty <;> simp only [argFrameAfter, List.mem_cons] at hb <;>
        (rcases hb with rfl | hb; exact ⟨i, rfl⟩; exact ih _ _ as b hb)

/-- The head call of a sealed program, after its arguments: the call on fresh borrows of the
cells. -/
theorem exec_sealHead (Pr : Prog) (k : Nat) {f : String} {d : FunDef} (hf : Pr.find f = some d)
    (hnp : d.ret ≠ .prop) (as : List Val) (w : Val) (N₀ : Nat)
    (hlen : d.params.length = as.length) (has : ∀ a ∈ as, a.loans = [] ∧ a ≠ .moved ∧ a.nb = 0) :
    exec Pr (k + 2) ⟨[argFrame 0 as ++ [(.hole, w)]], N₀⟩ (sealHead f d) =
      callWith (exec Pr (k + 1)) false f d (sealWs N₀ (d.params.map Prod.snd) as)
        ⟨[argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)]], N₀ + nRefs (d.params.map Prod.snd)⟩ := by
  have htys : (d.params.map Prod.snd).length = as.length := by simp [hlen]
  rw [sealHead, exec]
  simp only [hf, hnp, if_false]
  have h := execArgs_cells Pr k [(.hole, w)] (d.params.map Prod.snd) as 0 N₀ [] [] htys rfl has (by simp)
  simp only [List.append_nil, List.nil_append] at h
  rw [show tempFrame [] = [] from rfl, List.nil_append] at h
  rw [h, Res.bind_ok, sealArgTerms_length, tempFrame_eq_from]
  have hG : ∀ b ∈ argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)], ∀ j, b.1 ≠ Var.tmp j := by
    intro b hb j
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨i, hi⟩ := argFrameAfter_keys _ _ _ _ b hb; rw [hi]; simp
    · simp at hb; rw [hb]; simp
  have ht := takeTemps_tempFrameFrom (N₀ + nRefs (d.params.map Prod.snd)) _ hG
    (sealWs N₀ (d.params.map Prod.snd) as) 0
  rw [sealWs_length N₀ _ as htys, List.range_eq_range'] at *
  rw [ht]

end OchrMeta

/-! ## Part D: the sealed program's call is the original call, renamed -/

namespace OchrMeta

theorem Val.borrows_nil_of_nb {v : Val} (h : v.nb = 0) : v.borrows = [] := by
  induction v <;> simp_all [Val.nb, Val.borrows]

theorem Val.names_nil {v : Val} (hl : v.loans = []) (hb : v.nb = 0) : v.names = [] := by
  have hb' := Val.borrows_nil_of_nb hb
  cases h : v.names with
  | nil => rfl
  | cons x xs =>
    have hx : x ∈ v.names := by rw [h]; simp
    rcases Val.names_cases hx with h1 | h1 <;> simp_all

theorem Val.rename_of_names_nil {ρ : Nat → Nat} {v : Val} (h : v.names = []) : v.rename ρ = v := by
  induction v <;> simp_all [Val.rename, Val.names]

/-- Call arguments with the given borrow names at borrow positions. -/
def sealWsL : List Nat → List Ty → List Val → List Val
  | l :: ns, .ref _ :: tys, a :: as => .borrow l a :: sealWsL ns tys as
  | [], .ref _ :: _, _ => []
  | ns, ty :: tys, a :: as =>
    match ty with
    | .ref _ => []
    | _ => a :: sealWsL ns tys as
  | _, _, _ => []

theorem sealWs_eq : ∀ (c : Nat) (tys : List Ty) (as : List Val),
    sealWs c tys as = sealWsL (List.range' c (nRefs tys)) tys as := by
  intro c tys
  induction tys generalizing c with
  | nil => intro as; cases as <;> simp [sealWs, sealWsL, nRefs]
  | cons ty tys ih =>
    intro as
    cases as with
    | nil => cases ty <;> simp [sealWs, sealWsL, nRefs, List.range'_succ]
    | cons a as =>
      cases ty <;> simp [sealWs, sealWsL, nRefs, List.range'_succ, ih]

theorem sealArgs_eq : ∀ (i : Nat) (ps : List (Var × Ty)) (ws as : List Val) (ls : List (Nat × Nat)),
    sealArgs i ps ws = some (as, ls) → ws = sealWsL (ls.map Prod.snd) (ps.map Prod.snd) as := by
  intro i ps
  induction ps generalizing i with
  | nil =>
    intro ws as ls h
    cases ws with
    | nil => simp [sealArgs] at h; obtain ⟨rfl, rfl⟩ := h; simp [sealWsL]
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
            simp [sealWsL, ih (i + 1) ws as' ls' hr]
        | _ => simp [sealArgs] at h
      | _ =>
        simp only [sealArgs] at h
        cases hr : sealArgs (i + 1) ps ws with
        | none => rw [hr] at h; cases h
        | some q =>
          obtain ⟨as', ls'⟩ := q
          rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          simp [sealWsL, ih (i + 1) ws as' ls' hr]

theorem sealWsL_rename {ρ : Nat → Nat} : ∀ (ns : List Nat) (tys : List Ty) (as : List Val),
    (∀ a ∈ as, a.names = []) → (sealWsL ns tys as).map (Val.rename ρ) = sealWsL (ns.map ρ) tys as := by
  intro ns tys
  induction tys generalizing ns with
  | nil => intro as _; cases ns <;> cases as <;> simp [sealWsL]
  | cons ty tys ih =>
    intro as has
    cases as with
    | nil => cases ns <;> cases ty <;> simp [sealWsL]
    | cons a as =>
      have ha := Val.rename_of_names_nil (ρ := ρ) (has a (by simp))
      have has' := fun b hb => has b (List.mem_cons_of_mem _ hb)
      cases ty with
      | ref T =>
        cases ns with
        | nil => simp [sealWsL]
        | cons l ns => simp [sealWsL, Val.rename, ha, ih ns as has']
      | _ => simp [sealWsL, ha, ih ns as has']

end OchrMeta

namespace OchrMeta

theorem sealArgs_ls_length : ∀ (i : Nat) (ps : List (Var × Ty)) (ws as : List Val) (ls : List (Nat × Nat)),
    sealArgs i ps ws = some (as, ls) → ls.length = nRefs (ps.map Prod.snd) ∧ as.length = ps.length := by
  intro i ps
  induction ps generalizing i with
  | nil =>
    intro ws as ls h
    cases ws with
    | nil => simp [sealArgs] at h; obtain ⟨rfl, rfl⟩ := h; simp [nRefs]
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
            have := ih (i + 1) ws as' ls' hr
            simp [nRefs, this.1, this.2]
        | _ => simp [sealArgs] at h
      | _ =>
        simp only [sealArgs] at h
        cases hr : sealArgs (i + 1) ps ws with
        | none => rw [hr] at h; cases h
        | some q =>
          obtain ⟨as', ls'⟩ := q
          rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
          have := ih (i + 1) ws as' ls' hr
          simp [nRefs, this.1, this.2]

theorem relabel_map_src {src : List Nat} (hnd : src.Nodup) (base N δ : Nat) :
    src.map (relabel src base N δ) = List.range' base src.length := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
  exact relabel_src hnd j (by simpa using h1)

/-- **The sealed program's head call is the original call, renamed.**  Both runs, renamed onto
fresh canonical names `C, C+1, …` for the borrow arguments, are the same run. -/
theorem callRun_seal_canon (Pr : Prog) (n : Nat) (d : FunDef) (b : Term) {ws as : List Val}
    {ls : List (Nat × Nat)} (hsa : sealArgs 0 d.params ws = some (as, ls)) (has : ∀ a ∈ as, a.names = [])
    (hnd : (ls.map Prod.snd).Nodup) {N : Nat} (hN : ∀ l ∈ ls.map Prod.snd, l < N) (N₀ : Nat) :
    (callRun Pr n d b ws N).rename
        (relabel (ls.map Prod.snd) (max N (N₀ + ls.length)) N (max N (N₀ + ls.length) + ls.length - N))
        (max N (N₀ + ls.length) + ls.length - N) =
      (callRun Pr n d b (sealWs N₀ (d.params.map Prod.snd) as) (N₀ + ls.length)).rename
        (relabel (List.range' N₀ ls.length) (max N (N₀ + ls.length)) (N₀ + ls.length)
          (max N (N₀ + ls.length) + ls.length - (N₀ + ls.length)))
        (max N (N₀ + ls.length) + ls.length - (N₀ + ls.length)) := by
  obtain ⟨hk, _⟩ := sealArgs_ls_length 0 d.params ws as ls hsa
  have hws := sealArgs_eq 0 d.params ws as ls hsa
  have hCN : N ≤ max N (N₀ + ls.length) := Nat.le_max_left _ _
  have hC0 : N₀ + ls.length ≤ max N (N₀ + ls.length) := Nat.le_max_right _ _
  generalize max N (N₀ + ls.length) = C at hCN hC0 ⊢
  generalize hkk : ls.length = k at hC0 hk ⊢
  -- left: the original call
  have hl := callRun_rename (ρ := relabel (ls.map Prod.snd) C N (C + k - N)) Pr n d b ws
    (relabel_inj hCN (by simp; omega)) (relabel_cc hN)
  rw [← hl]
  -- right: the sealed program's call
  have hsrc : ∀ l ∈ List.range' N₀ k, l < N₀ + k := by intro l hl; simp [List.mem_range'] at hl; omega
  have hr := callRun_rename (ρ := relabel (List.range' N₀ k) C (N₀ + k) (C + k - (N₀ + k))) Pr n d b
    (sealWs N₀ (d.params.map Prod.snd) as) (relabel_inj hC0 (by simp; omega)) (relabel_cc hsrc)
  rw [← hr]
  have e1 : N + (C + k - N) = C + k := by omega
  have e2 : N₀ + k + (C + k - (N₀ + k)) = C + k := by omega
  rw [e1, e2, hws, sealWsL_rename _ _ _ has, sealWs_eq, sealWsL_rename _ _ _ has, ← hk,
    relabel_map_src hnd, relabel_map_src List.nodup_range']
  simp [hkk]

end OchrMeta
