import OchrMeta.Rename
import OchrMeta.Interp
import OchrMeta.Mono

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

/-! ## Part E: the tails of the sealed programs -/

namespace OchrMeta

theorem Val.toList_ofList : ∀ as : List Val, (Val.ofList as).toList = as := by
  intro as; induction as <;> simp_all [Val.ofList, Val.toList]

theorem argFrameAfter_vals : ∀ (i c : Nat) (tys : List Ty) (as : List Val),
    ∀ b ∈ argFrameAfter i c tys as, (∃ l, c ≤ l ∧ l < c + nRefs tys ∧ b.2 = .loan l) ∨ b.2 ∈ as := by
  intro i c tys
  induction tys generalizing i c with
  | nil => intro as b hb; simp [argFrameAfter] at hb
  | cons ty tys ih =>
    intro as b hb
    cases as with
    | nil => cases ty <;> simp [argFrameAfter] at hb
    | cons a as =>
      cases ty with
      | ref T =>
        simp only [argFrameAfter, List.mem_cons] at hb
        rcases hb with rfl | hb
        · left; exact ⟨c, Nat.le_refl _, by simp [nRefs], rfl⟩
        · rcases ih _ _ as b hb with ⟨l, h1, h2, h3⟩ | h
          · left; exact ⟨l, by omega, by simp [nRefs]; omega, h3⟩
          · right; exact List.mem_cons_of_mem _ h
      | _ =>
        simp only [argFrameAfter, List.mem_cons] at hb
        rcases hb with rfl | hb
        · right; simp
        · rcases ih _ _ as b hb with ⟨l, h1, h2, h3⟩ | h
          · left; exact ⟨l, h1, by simpa [nRefs] using h2, h3⟩
          · right; exact List.mem_cons_of_mem _ h

/-- T2b inside the sealed program: its head call, after the arguments, is the isolated run of
the call on fresh borrows `N₀, N₀+1, …`, plugged back into the cells. -/
theorem seal_call_effect (Pr : Prog) (k : Nat) (f : String) {d : FunDef} {b : Term} (hb : d.body = some b)
    (as : List Val) (w : Val) (N₀ : Nat) (hlen : d.params.length = as.length)
    (has : ∀ a ∈ as, a.loans = [] ∧ a ≠ .moved ∧ a.nb = 0) (hw : ∀ l ∈ w.names, l < N₀) (hwnb : w.nb = 0) :
    callWith (exec Pr k) false f d (sealWs N₀ (d.params.map Prod.snd) as)
        ⟨[argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)]], N₀ + nRefs (d.params.map Prod.snd)⟩ =
      match callRun Pr k d b (sealWs N₀ (d.params.map Prod.snd) as) (N₀ + nRefs (d.params.map Prod.snd)) with
      | .ok s' v => .ok (frameMap (Env.portKeys [paramFrame d (sealWs N₀ (d.params.map Prod.snd) as)])
          [argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)]] s') v
      | .stuck => .stuck
      | .err => .err
      | .oof => .oof := by
  have htys : (d.params.map Prod.snd).length = as.length := by simp [hlen]
  have hasn : ∀ a ∈ as, a.names = [] := fun a h => Val.names_nil (has a h).1 (has a h).2.2
  -- the cells' frame holds no borrow
  have hnb : ∀ b ∈ argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)], b.2.nb = 0 := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · rcases argFrameAfter_vals _ _ _ _ b hb with ⟨l, _, _, h⟩ | h
      · rw [h]; rfl
      · exact (has _ h).2.2
    · simp at hb; rw [hb]; exact hwnb
  have hnh : ∀ l, Env.holds l [argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)]] = false := by
    intro l
    simp only [Env.holds, List.any_cons, List.any_nil, Bool.or_false, Frame.holds, List.any_eq_false]
    intro b hb h
    rw [Val.not_isBorrowOf_of_nb (hnb b hb)] at h
    cases h
  have hws : ∀ v ∈ sealWs N₀ (d.params.map Prod.snd) as, v.loans = [] := by
    rw [sealWs_eq]
    generalize List.range' N₀ (nRefs (d.params.map Prod.snd)) = ns
    clear hlen htys hasn hnb hnh
    induction (d.params.map Prod.snd) generalizing ns as with
    | nil => intro v hv; cases ns <;> cases as <;> simp [sealWsL] at hv
    | cons ty tys ih =>
      intro v hv
      cases as with
      | nil => cases ns <;> cases ty <;> simp [sealWsL] at hv
      | cons a as =>
        have ha := has a (by simp)
        have has' := fun b hb => has b (List.mem_cons_of_mem a hb)
        cases ty with
        | ref T =>
          cases ns with
          | nil => simp [sealWsL] at hv
          | cons l ns =>
            simp only [sealWsL, List.mem_cons] at hv
            rcases hv with rfl | hv
            · simp [Val.loans, ha.1]
            · exact ih as has' ns v hv
        | _ =>
          simp only [sealWsL, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ha.1
          · exact ih as has' ns v hv
  have hce := call_effect Pr k false f hb (ws := sealWs N₀ (d.params.map Prod.snd) as)
    (by rw [sealWs_length _ _ _ htys]; simp)
    ⟨[argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(.hole, w)]], N₀ + nRefs (d.params.map Prod.snd)⟩
    (fun _ _ l _ => hnh l)
    (fun v hv l hl => by rw [hws v hv] at hl; cases hl)
    (by
      intro l hl
      show l < N₀ + nRefs (d.params.map Prod.snd)
      rw [Env.mem_names] at hl
      obtain ⟨F, hF, b, hb, hlb⟩ := hl
      simp at hF; subst hF
      rcases List.mem_append.mp hb with hb | hb
      · rcases argFrameAfter_vals _ _ _ _ b hb with ⟨l', _, h2, h⟩ | h
        · rw [h] at hlb; simp [Val.names] at hlb; omega
        · rw [hasn _ h] at hlb; cases hlb
      · simp at hb; rw [hb] at hlb; have := hw l hlb; omega)
  rw [hce]
  cases callRun Pr k d b (sealWs N₀ (d.params.map Prod.snd) as) (N₀ + nRefs (d.params.map Prod.snd)) <;> rfl

end OchrMeta

namespace OchrMeta

/-- Unfolding `sealArgs` one parameter at a time. -/
theorem sealArgs_cons_ref {i : Nat} {y : Var} {T : Ty} {ps : List (Var × Ty)} {w : Val} {ws as : List Val}
    {ls : List (Nat × Nat)} (h : sealArgs i ((y, .ref T) :: ps) (w :: ws) = some (as, ls)) :
    ∃ l u as' ls', w = .borrow l u ∧ sealArgs (i + 1) ps ws = some (as', ls') ∧ as = u :: as' ∧ ls = (i, l) :: ls' := by
  cases w with
  | borrow l u =>
    simp only [sealArgs] at h
    cases hr : sealArgs (i + 1) ps ws with
    | none => rw [hr] at h; cases h
    | some q =>
      obtain ⟨as', ls'⟩ := q
      rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨l, u, as', ls', rfl, rfl, rfl, rfl⟩
  | _ => simp [sealArgs] at h

theorem sealArgs_cons_val {i : Nat} {y : Var} {ty : Ty} (hty : ∀ T, ty ≠ .ref T) {ps : List (Var × Ty)} {w : Val}
    {ws as : List Val} {ls : List (Nat × Nat)} (h : sealArgs i ((y, ty) :: ps) (w :: ws) = some (as, ls)) :
    ∃ as', sealArgs (i + 1) ps ws = some (as', ls) ∧ as = w :: as' := by
  cases ty with
  | ref T => exact absurd rfl (hty T)
  | _ =>
    simp only [sealArgs] at h
    cases hr : sealArgs (i + 1) ps ws with
    | none => rw [hr] at h; cases h
    | some q =>
      obtain ⟨as', ls'⟩ := q
      rw [hr] at h; simp at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨as', rfl, rfl⟩

theorem sealArgs_pos : ∀ (i₀ : Nat) (ps : List (Var × Ty)) (ws as : List Val) (ls : List (Nat × Nat)),
    sealArgs i₀ ps ws = some (as, ls) → ∀ q ∈ ls, i₀ ≤ q.1 := by
  intro i₀ ps
  induction ps generalizing i₀ with
  | nil => intro ws as ls h; cases ws <;> simp [sealArgs] at h; obtain ⟨_, rfl⟩ := h; simp
  | cons p ps ih =>
    intro ws as ls h q hq
    obtain ⟨y, ty⟩ := p
    cases ws with
    | nil => cases ty <;> simp [sealArgs] at h
    | cons w ws =>
      by_cases hty : ∃ T, ty = .ref T
      · obtain ⟨T, rfl⟩ := hty
        obtain ⟨l, u, as', ls', rfl, hr, rfl, rfl⟩ := sealArgs_cons_ref h
        rcases List.mem_cons.mp hq with rfl | hq
        · simp
        · have := ih (i₀ + 1) ws as' ls' hr q hq; omega
      · have hty' : ∀ T, ty ≠ .ref T := fun T h => hty ⟨T, h⟩
        obtain ⟨as', hr, rfl⟩ := sealArgs_cons_val hty' h
        have := ih (i₀ + 1) ws as' ls hr q hq; omega

theorem sealArgs_cell : ∀ (i₀ : Nat) (ps : List (Var × Ty)) (ws as : List Val) (ls : List (Nat × Nat)) (c : Nat),
    sealArgs i₀ ps ws = some (as, ls) → ∀ (j i ℓ : Nat), ls[j]? = some (i, ℓ) →
      (argFrameAfter i₀ c (ps.map Prod.snd) as).lookup (Var.arg i) = some (.loan (c + j)) := by
  intro i₀ ps
  induction ps generalizing i₀ with
  | nil =>
    intro ws as ls c h
    cases ws with
    | nil => simp [sealArgs] at h; obtain ⟨rfl, rfl⟩ := h; simp
    | cons w ws => simp [sealArgs] at h
  | cons p ps ih =>
    intro ws as ls c h j i ℓ hj
    obtain ⟨y, ty⟩ := p
    cases ws with
    | nil => cases ty <;> simp [sealArgs] at h
    | cons w ws =>
      by_cases hty : ∃ T, ty = .ref T
      · obtain ⟨T, rfl⟩ := hty
        obtain ⟨l, u, as', ls', rfl, hr, rfl, rfl⟩ := sealArgs_cons_ref h
        cases j with
        | zero =>
          simp at hj; obtain ⟨rfl, rfl⟩ := hj
          simp [argFrameAfter]
        | succ j =>
          simp at hj
          have hlt : i₀ < i := by
            have := sealArgs_pos (i₀ + 1) ps ws as' ls' hr (i, ℓ) (List.mem_of_getElem? hj)
            simp at this; omega
          have : (Var.arg i == Var.arg i₀) = false := by simp; omega
          simp only [List.map_cons, argFrameAfter, List.lookup_cons, this, Bool.false_eq_true, if_false]
          rw [ih (i₀ + 1) ws as' ls' (c + 1) hr j i ℓ hj]
          congr 2; omega
      · have hty' : ∀ T, ty ≠ .ref T := fun T h => hty ⟨T, h⟩
        obtain ⟨as', hr, rfl⟩ := sealArgs_cons_val hty' h
        have hlt : i₀ < i := by
          have := sealArgs_pos (i₀ + 1) ps ws as' ls hr (i, ℓ) (List.mem_of_getElem? hj)
          simp at this; omega
        have : (Var.arg i == Var.arg i₀) = false := by simp; omega
        have hA : argFrameAfter i₀ c (ty :: ps.map Prod.snd) (w :: as') =
            (Var.arg i₀, w) :: argFrameAfter (i₀ + 1) c (ps.map Prod.snd) as' := by
          cases ty with
          | ref T => exact absurd rfl (hty' T)
          | _ => rfl
        simp only [List.map_cons]
        rw [hA]
        simp only [List.lookup_cons, this, Bool.false_eq_true, if_false]
        exact ih (i₀ + 1) ws as' ls c hr j i ℓ hj

end OchrMeta

namespace OchrMeta

theorem Frame.borrows_zip : ∀ (xs : List Var) (vs : List Val), vs.length ≤ xs.length →
    Frame.borrows (xs.zip vs) = vs.flatMap Val.borrows := by
  intro xs
  induction xs with
  | nil => intro vs h; cases vs <;> simp_all [Frame.borrows]
  | cons x xs ih =>
    intro vs h
    cases vs with
    | nil => simp [Frame.borrows]
    | cons v vs => simp [Frame.borrows, ih vs (by simp at h; omega)]

theorem sealWsL_borrows : ∀ (ns : List Nat) (tys : List Ty) (as : List Val),
    (∀ a ∈ as, a.names = []) → ns.length = nRefs tys → tys.length = as.length →
    (sealWsL ns tys as).flatMap Val.borrows = ns := by
  intro ns tys
  induction tys generalizing ns with
  | nil => intro as _ hn hl; cases as <;> cases ns <;> simp_all [sealWsL, nRefs]
  | cons ty tys ih =>
    intro as has hn hl
    cases as with
    | nil => simp at hl
    | cons a as =>
      have ha : a.borrows = [] := by
        have := has a (by simp)
        cases hb : a.borrows with
        | nil => rfl
        | cons x xs =>
          have hx : x ∈ a.names := by
            have : x ∈ a.borrows := by rw [hb]; simp
            clear hb
            induction a <;> simp_all [Val.borrows, Val.names] <;> grind
          rw [this] at hx; cases hx
      have has' := fun b hb => has b (List.mem_cons_of_mem a hb)
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      cases ty with
      | ref T =>
        cases ns with
        | nil => simp [nRefs] at hn
        | cons l ns =>
          simp only [nRefs, List.length_cons, Nat.add_right_cancel_iff] at hn
          simp [sealWsL, Val.borrows, ha, ih ns as has' hn hl]
      | _ =>
        simp only [nRefs] at hn
        simp [sealWsL, ha, ih ns as has' hn hl]

theorem sealWsL_length : ∀ (ns : List Nat) (tys : List Ty) (as : List Val),
    ns.length = nRefs tys → tys.length = as.length → (sealWsL ns tys as).length = tys.length := by
  intro ns tys
  induction tys generalizing ns with
  | nil => intro as hn hl; cases as <;> cases ns <;> simp_all [sealWsL]
  | cons ty tys ih =>
    intro as hn hl
    cases as with
    | nil => simp at hl
    | cons a as =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      cases ty with
      | ref T =>
        cases ns with
        | nil => simp [nRefs] at hn
        | cons l ns =>
          simp only [nRefs, List.length_cons, Nat.add_right_cancel_iff] at hn
          simp [sealWsL, ih ns as hn hl]
      | _ =>
        simp only [nRefs] at hn
        simp [sealWsL, ih ns as hn hl]

/-- The port keys of the generic environment of a call on arguments with borrow names `ns`. -/
theorem portKeys_sealWsL (d : FunDef) (ns : List Nat) (as : List Val) (has : ∀ a ∈ as, a.names = [])
    (hn : ns.length = nRefs (d.params.map Prod.snd)) (hl : d.params.length = as.length) :
    Env.portKeys [paramFrame d (sealWsL ns (d.params.map Prod.snd) as)] = ns := by
  have hl' : (d.params.map Prod.snd).length = as.length := by simp [hl]
  simp only [Env.portKeys, Env.borrows, paramFrame, List.append_nil]
  rw [Frame.borrows_zip _ _ (by rw [sealWsL_length ns _ as hn hl']; simp), sealWsL_borrows ns _ as has hn hl']

end OchrMeta

namespace OchrMeta

theorem sealWs_eq_L (N₀ : Nat) (d : FunDef) (as : List Val) :
    sealWs N₀ (d.params.map Prod.snd) as = sealWsL (List.range' N₀ (nRefs (d.params.map Prod.snd))) (d.params.map Prod.snd) as :=
  sealWs_eq _ _ _

theorem Val.loans_nil_of_names {v : Val} (h : v.names = []) : v.loans = [] := by
  cases hl : v.loans with
  | nil => rfl
  | cons x xs =>
    have : x ∈ v.names := Val.loans_sub_names (by rw [hl]; simp)
    rw [h] at this; cases this

theorem Val.nb_of_names_nil {v : Val} (h : v.names = []) : v.nb = 0 := by
  induction v <;> simp_all [Val.names, Val.nb]

/-- The cells after the call: each borrowed cell holds the final content of its port. -/
theorem cell_after_call {F : Frame} {i N₀ j k : Nat} {P' : Frame} {φ : Val}
    (hF : F.lookup (Var.arg i) = some (.loan (N₀ + j))) (hj : j < k)
    (hφ : P'.lookup (.port j) = some φ) :
    (F.mapVals (Val.substSim (portSub (List.range' N₀ k) P'))).lookup (Var.arg i) = some φ := by
  rw [Frame.lookup_mapVals, hF]
  simp only [Option.map_some, Val.substSim, portSub]
  have : (List.range' N₀ k).idxOf? (N₀ + j) = some j := by
    rw [List.idxOf?_eq_some_iff]
    refine ⟨by simp; omega, by simp, fun j' hj' heq => ?_⟩
    simp at heq; omega
  rw [this]
  simp [hφ]

theorem lookup_append_of_some {A B : Frame} {x : Var} {v : Val} (h : A.lookup x = some v) :
    (A ++ B).lookup x = some v := by
  induction A with
  | nil => simp at h
  | cons b A ih =>
    obtain ⟨y, w⟩ := b
    simp only [List.cons_append, List.lookup_cons] at h ⊢
    split at h
    · simp_all
    · simp_all

/-- **The [Close] equation for the fill of a borrowed place** (row `fin i`), on the sealed
program's side: once its head call has completed with a name-free result, the sealed program
`⌈L; C; cᵢ⌉` normalises to the final content of the `j`-th borrowed cell. -/
theorem sealRun_fin (Pr : Prog) (m : Nat) {f : String} {d : FunDef} {b : Term}
    (hf : Pr.find f = some d) (hb : d.body = some b) (hnp : d.ret ≠ .prop)
    {ws as : List Val} {ls : List (Nat × Nat)} (hsa : sealArgs 0 d.params ws = some (as, ls))
    (has : ∀ a ∈ as, a.loans = [] ∧ a ≠ .moved ∧ a.nb = 0)
    {j i ℓ : Nat} (hj : ls[j]? = some (i, ℓ)) {s' : St} {v' : Val} {P' : Frame} {φ : Val}
    (hrun : callRun Pr (m + 1) d b
      (sealWs (Val.pair (Val.ofList as) .unit).freshAbove (d.params.map Prod.snd) as)
      ((Val.pair (Val.ofList as) .unit).freshAbove + nRefs (d.params.map Prod.snd)) = .ok s' v')
    (hs' : s'.env = [P']) (hv' : v'.names = []) (hφ : P'.lookup (.port j) = some φ)
    (hφn : φ.names = []) (hφm : φ ≠ .moved) :
    ∃ s'', sealRun Pr (m + 3) f (Val.ofList as) (.fin i) .unit = .ok s'' φ := by
  generalize hN₀ : (Val.pair (Val.ofList as) .unit).freshAbove = N₀ at hrun
  obtain ⟨hk, hlen⟩ := sealArgs_ls_length 0 d.params ws as ls hsa
  have hasn : ∀ a ∈ as, a.names = [] := fun a h => Val.names_nil (has a h).1 (has a h).2.2
  have hjk : j < nRefs (d.params.map Prod.snd) := by
    rw [← hk]; exact (List.getElem?_eq_some_iff.mp hj).1
  unfold sealRun
  rw [hf]
  simp only [sealFrame, Val.toList_ofList, sealTerm, hN₀]
  rw [exec]
  rw [exec_sealHead Pr m hf hnp as .unit N₀ hlen.symm has, seal_call_effect Pr (m + 1) f hb as .unit N₀ hlen.symm has
    (by simp [Val.names]) rfl, hrun]
  simp only
  -- the head call's value is dropped
  have hdrop : ∀ s, dropVal .unit v' s = some s := by
    intro s
    have hl : v'.loans = [] := by
      cases h : v'.loans with
      | nil => rfl
      | cons x xs => have : x ∈ v'.names := Val.loans_sub_names (by rw [h]; simp)
                     rw [hv'] at this; cases this
    have hnb : ¬ ∃ l w, v' = .borrow l w := by
      rintro ⟨l, w, rfl⟩; simp [Val.names] at hv'
    cases v' with
    | borrow l w => exact absurd ⟨l, w, rfl⟩ hnb
    | _ => simp [dropVal, hasLive, Val.firstLive_noloans hl]
  rw [Res.bind_ok, hdrop]
  -- the final read of the cell
  have hK : Env.portKeys [paramFrame d (sealWs N₀ (d.params.map Prod.snd) as)] =
      List.range' N₀ (nRefs (d.params.map Prod.snd)) := by
    rw [sealWs_eq_L]; exact portKeys_sealWsL d _ as hasn (by simp) hlen.symm
  have hfm : frameMap (Env.portKeys [paramFrame d (sealWs N₀ (d.params.map Prod.snd) as)])
      [argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(Var.hole, Val.unit)]] s' =
      ⟨[(argFrameAfter 0 N₀ (d.params.map Prod.snd) as ++ [(Var.hole, Val.unit)]).mapVals
        (Val.substSim (portSub (List.range' N₀ (nRefs (d.params.map Prod.snd))) P'))], s'.next⟩ := by
    simp [frameMap, hs', hK, Env.substPorts, Env.mapVals]
  rw [hfm]
  have hcell := sealArgs_cell 0 d.params ws as ls N₀ hsa j i ℓ hj
  have hlk := cell_after_call (lookup_append_of_some (B := [(.hole, .unit)]) hcell) hjk hφ
  have hφl : φ.loans = [] := Val.loans_nil_of_names hφn
  have hφb : φ.nb = 0 := Val.nb_of_names_nil hφn
  exact ⟨_, exec_read_cell Pr (m + 1) hlk hφl hφm hφb⟩

end OchrMeta

namespace OchrMeta

theorem Val.names_rename (ρ : Nat → Nat) (v : Val) : (v.rename ρ).names = v.names.map ρ := by
  induction v <;> simp_all [Val.rename, Val.names]

theorem Val.names_nil_of_rename {ρ : Nat → Nat} {v : Val} {u : Val} (h : v.rename ρ = u) (hu : u.names = []) :
    v.names = [] := by
  have := Val.names_rename ρ v
  rw [h, hu] at this
  exact List.map_eq_nil_iff.mp this.symm

/-- More fuel does not change a terminated isolated call run. -/
theorem callRun_mono (Pr : Prog) {n m : Nat} (h : n ≤ m) {d : FunDef} {b : Term} {ws : List Val} {N : Nat}
    (hr : callRun Pr n d b ws N ≠ .oof) : callRun Pr m d b ws N = callRun Pr n d b ws N := by
  unfold callRun at hr ⊢
  have he : exec Pr n ⟨[paramFrame d ws, Env.portsOf [paramFrame d ws]], N⟩ b ≠ .oof := by
    intro h'; rw [h'] at hr; exact hr rfl
  rw [exec_mono_le Pr h he]

/-- From the canonical bridge: a completed original call gives a completed sealed call, related
by renaming. -/
theorem callRun_seal_ok (Pr : Prog) (n : Nat) (d : FunDef) (b : Term) {ws as : List Val}
    {ls : List (Nat × Nat)} (hsa : sealArgs 0 d.params ws = some (as, ls)) (has : ∀ a ∈ as, a.names = [])
    (hnd : (ls.map Prod.snd).Nodup) {N : Nat} (hN : ∀ l ∈ ls.map Prod.snd, l < N) (N₀ : Nat)
    {s : St} {v : Val} (hrun : callRun Pr n d b ws N = .ok s v) :
    ∃ ρ₁ ρ₂ : Nat → Nat, ∃ s' v', callRun Pr n d b (sealWs N₀ (d.params.map Prod.snd) as) (N₀ + ls.length) = .ok s' v' ∧
      s'.env.rename ρ₂ = s.env.rename ρ₁ ∧ v'.rename ρ₂ = v.rename ρ₁ := by
  have h := callRun_seal_canon Pr n d b hsa has hnd hN N₀
  rw [hrun] at h
  simp only [Res.rename_ok] at h
  revert h
  cases callRun Pr n d b (sealWs N₀ (d.params.map Prod.snd) as) (N₀ + ls.length) with
  | ok s' v' =>
    intro h
    simp only [Res.rename_ok, Res.ok.injEq] at h
    exact ⟨_, _, s', v', rfl, (congrArg St.env h.1).symm, h.2.symm⟩
  | stuck => intro h; cases h
  | err => intro h; cases h
  | oof => intro h; cases h

end OchrMeta

namespace OchrMeta

/-- A single-frame environment renamed. -/
theorem env_single_of_rename {ρ₁ ρ₂ : Nat → Nat} {E : Env} {P : Frame} (h : E.rename ρ₂ = Env.rename ρ₁ [P]) :
    ∃ P', E = [P'] ∧ P'.mapVals (Val.rename ρ₂) = P.mapVals (Val.rename ρ₁) := by
  cases E with
  | nil => simp [Env.rename, Env.mapVals] at h
  | cons F E =>
    cases E with
    | nil =>
      simp only [Env.rename, Env.mapVals, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨F, rfl, h⟩
    | cons G E => simp [Env.rename, Env.mapVals] at h

theorem port_of_rename {ρ₁ ρ₂ : Nat → Nat} {P P' : Frame} (h : P'.mapVals (Val.rename ρ₂) = P.mapVals (Val.rename ρ₁))
    {x : Var} {φ : Val} (hφ : P.lookup x = some φ) (hφn : φ.names = []) : P'.lookup x = some φ := by
  have h1 := congrArg (fun F : Frame => F.lookup x) h
  simp only [Frame.lookup_mapVals, hφ, Option.map_some] at h1
  rw [Val.rename_of_names_nil hφn] at h1
  cases hp : P'.lookup x with
  | none => rw [hp] at h1; cases h1
  | some φ' =>
    rw [hp] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    have hn := Val.names_nil_of_rename h1 hφn
    rw [Val.rename_of_names_nil hn] at h1
    rw [h1]

/-- **[Close] equation, row `fin i`** (the fill of a borrowed place, `⌈L; C; cᵢ⌉`).  If the call's
isolated run completes with a name-free result and the `j`-th borrowed place's final content is
`φ`, then the sealed program [Close] writes into that place normalises (by [Seal]) to `φ`. -/
theorem close_fin (Pr : Prog) {n : Nat} {f : String} {d : FunDef} {b : Term}
    (hf : Pr.find f = some d) (hb : d.body = some b) (hnp : d.ret ≠ .prop)
    {ws as : List Val} {ls : List (Nat × Nat)} (hsa : sealArgs 0 d.params ws = some (as, ls))
    (has : ∀ a ∈ as, a.loans = [] ∧ a ≠ .moved ∧ a.nb = 0)
    (hnd : (ls.map Prod.snd).Nodup) {N : Nat} (hN : ∀ l ∈ ls.map Prod.snd, l < N)
    {s : St} {v : Val} {P : Frame} (hrun : callRun Pr n d b ws N = .ok s v)
    (hs : s.env = [P]) (hv : v.names = [])
    {j i ℓ : Nat} (hj : ls[j]? = some (i, ℓ)) {φ : Val} (hφ : P.lookup (.port j) = some φ)
    (hφn : φ.names = []) (hφm : φ ≠ .moved) :
    ∀ m, n ≤ m + 1 → ∃ s'', sealRun Pr (m + 3) f (Val.ofList as) (.fin i) .unit = .ok s'' φ := by
  intro m hm
  have hasn : ∀ a ∈ as, a.names = [] := fun a h => Val.names_nil (has a h).1 (has a h).2.2
  obtain ⟨hk, _⟩ := sealArgs_ls_length 0 d.params ws as ls hsa
  have hrun' : callRun Pr (m + 1) d b ws N = .ok s v := by
    rw [callRun_mono Pr hm (by rw [hrun]; simp)]; exact hrun
  obtain ⟨ρ₁, ρ₂, s', v', hr', hse, hve⟩ :=
    callRun_seal_ok Pr (m + 1) d b hsa hasn hnd hN (Val.pair (Val.ofList as) .unit).freshAbove hrun'
  rw [hk] at hr'
  rw [hs] at hse
  obtain ⟨P', hs', hPP⟩ := env_single_of_rename hse
  have hv' : v'.names = [] := Val.names_nil_of_rename (u := v) (by rw [hve, Val.rename_of_names_nil hv]) hv
  exact sealRun_fin Pr m hf hb hnp hsa has hj hr' hs' hv' (port_of_rename hPP hφ hφn) hφn hφm

end OchrMeta
