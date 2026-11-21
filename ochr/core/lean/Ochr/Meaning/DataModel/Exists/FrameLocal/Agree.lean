import Ochr.Meaning.DataModel.Exists.FrameLocal.Setup
import Ochr.Meaning.Locality

/-!
# Frame locality, part 5a: descriptions that agree at arguments of the right length (exists4)

A Π's or a closure's parameters are described by functions of the earlier arguments (`PBind`,
`PiDom`, `PiCod`, the body's `g`), defined at EVERY list of arguments. The run of a domain term at a
list of the wrong length pushes the wrong number of bindings, so the term's variables name other
bindings of the frame, possibly ones frame locality varies: the two sides of `runT_qset` then give
descriptions that agree only at lists of the right length. Every consumer reads them only there
(the telescope code `telL`, `piProp`, `PiOk`, the closure's element `mkTelL`, the pushed parameters
`extendBinds`), so the consumers agree. This file proves that.
-/

namespace Ochr.Meaning.DataModel.Exists.FrameLocal

open Ochr Ochr.Meaning

/-- Two telescope descriptions agree at arguments of the right length, `n` arguments in. -/
def DomAgree (n : Nat) (ps ps' : List PiDom) : Prop :=
  ps.length = ps'.length ∧ ∀ (i : Nat) (p p' : PiDom), ps[i]? = some p → ps'[i]? = some p' →
    p.isRef = p'.isRef ∧ ∀ acc : List Sem, acc.length = n + i → p.dom acc = p'.dom acc

/-- Two codomains agree at `n` arguments. -/
def CodAgree (n : Nat) (out out' : PiCod) : Prop :=
  out.isRef = out'.isRef ∧ ∀ acc : List Sem, acc.length = n → out.cod acc = out'.cod acc

theorem DomAgree.refl (n : Nat) (ps : List PiDom) : DomAgree n ps ps :=
  ⟨rfl, fun _ p p' h h' => by rw [h] at h'; cases h'; exact ⟨rfl, fun _ _ => rfl⟩⟩

theorem DomAgree.head {n : Nat} {p p' : PiDom} {ps ps' : List PiDom} (h : DomAgree n (p :: ps) (p' :: ps')) :
    p.isRef = p'.isRef ∧ ∀ acc : List Sem, acc.length = n → p.dom acc = p'.dom acc := by
  obtain ⟨hr, hd⟩ := h.2 0 p p' rfl rfl
  exact ⟨hr, fun acc ha => hd acc (by omega)⟩

theorem DomAgree.tail {n : Nat} {p p' : PiDom} {ps ps' : List PiDom} (h : DomAgree n (p :: ps) (p' :: ps')) :
    DomAgree (n + 1) ps ps' := by
  refine ⟨by simpa using h.1, fun i q q' hq hq' => ?_⟩
  obtain ⟨hr, hd⟩ := h.2 (i + 1) q q' (by simpa using hq) (by simpa using hq')
  exact ⟨hr, fun acc ha => hd acc (by omega)⟩

section
universe u
variable (Lv : Lvl.{u})

/-- One parameter of a telescope code, from its kind, its domain and the rest at each argument. -/
def telStep (Fin : Type u) (r : Bool) (T : TyM) (H : (F : Type u) → Sem → (C : Type u) × Tel Lv.Code F C) :
    (C : Type u) × Tel Lv.Code Fin C :=
  ⟨(a : (Lv.codeOf T).1) → (H (extFin r Fin (Lv.codeOf T).1) (Lv.enc (Lv.codeOf T).2 a)).1,
    .param Fin r _ (Lv.codeOf T).2 _ fun a => (H (extFin r Fin (Lv.codeOf T).1) (Lv.enc (Lv.codeOf T).2 a)).2⟩

theorem telL_cons (p : PiDom) (ps : List PiDom) (acc : List Sem) (Fin : Type u) (out : PiCod) :
    telL Lv (p :: ps) acc Fin out = telStep Lv Fin p.isRef (p.dom acc) (fun F x => telL Lv ps (acc ++ [x]) F out) :=
  rfl

/-- **The telescope code reads each domain at the right number of arguments.** -/
theorem telL_congr : ∀ (ds ds' : List PiDom) (acc : List Sem) (Fin : Type u) (out out' : PiCod),
    DomAgree acc.length ds ds' → CodAgree (acc.length + ds.length) out out' →
    telL Lv ds acc Fin out = telL Lv ds' acc Fin out'
  | [], [], acc, Fin, ⟨b, c⟩, ⟨b', c'⟩, _, ⟨hr, hc⟩ => by
    dsimp only at hr; subst hr
    have e : c acc = c' acc := hc acc (by simp)
    cases b <;> (simp only [telL]; rw [e])
  | [], _ :: _, _, _, _, _, h, _ => absurd h.1 (by simp)
  | _ :: _, [], _, _, _, _, h, _ => absurd h.1 (by simp)
  | p :: ps, p' :: ps', acc, Fin, out, out', h, hc => by
    obtain ⟨hr, hd⟩ := h.head
    rw [telL_cons, telL_cons, hr, hd acc rfl]
    have hH : (fun F x => telL Lv ps (acc ++ [x]) F out) = (fun F x => telL Lv ps' (acc ++ [x]) F out') :=
      funext fun F => funext fun x => telL_congr ps ps' (acc ++ [x]) F out out' (by simpa using h.tail)
        ⟨hc.1, fun a ha => hc.2 a (by simp at ha ⊢; omega)⟩
    rw [hH]

/-- The number of parameters of a telescope code (every leaf is reached after `n`). -/
def TelAr : {Fin C : Type u} → Tel Lv.Code Fin C → Nat → Prop
  | _, _, .dat .., n => n = 0
  | _, _, .ref .., n => n = 0
  | _, _, .param _ _ _ _ _ k, n => ∃ m, n = m + 1 ∧ ∀ a, TelAr (k a) m

theorem telL_ar : ∀ (ds : List PiDom) (acc : List Sem) (Fin : Type u) (out : PiCod),
    TelAr Lv (telL Lv ds acc Fin out).2 ds.length
  | [], acc, Fin, ⟨b, cod⟩ => by cases b <;> simp only [telL, TelAr, List.length_nil]
  | p :: ps, acc, Fin, out => ⟨ps.length, rfl, fun _ => telL_ar ps _ _ out⟩

/-- **A closure's element reads its body's outputs only at full argument lists.** -/
theorem mkTelL_g_congr (φ : Future) : ∀ {Fin C : Type u} (t : Tel Lv.Code Fin C) (n : Nat), TelAr Lv t n →
    ∀ (acc : List Sem) (mkFin : List Sem → Option (Fin × List Sem)) (g g' : List Sem → Option BodyOut),
    (∀ a : List Sem, a.length = acc.length + n → g a = g' a) →
    mkTelL Lv φ t acc mkFin g = mkTelL Lv φ t acc mkFin g'
  | _, _, .dat Fin B c, n, hn, acc, mkFin, g, g', hg => by
    simp only [TelAr] at hn; subst hn; simp only [mkTelL]; rw [hg acc (by simp)]
  | _, _, .ref Fin U c, n, hn, acc, mkFin, g, g', hg => by
    simp only [TelAr] at hn; subst hn; simp only [mkTelL]; rw [hg acc (by simp)]
  | _, _, .param Fin isR A c C k, n, ⟨m, hm, hk⟩, acc, mkFin, g, g', hg => by
    simp only [mkTelL]
    exact dite_isSome_congr _ _ (funext fun x => mkTelL_g_congr φ (k x) m (hk x) _ _ g g' fun a ha =>
      hg a (by simp at ha; omega))

end

/-- `piProp` reads each domain, and the proposition, at the right number of arguments. -/
theorem piProp_congr (R : DataRead) : ∀ (ps ps' : List PiDom) (acc : List Sem) (P P' : List Sem → Prop),
    DomAgree acc.length ps ps' → (∀ a : List Sem, a.length = acc.length + ps.length → P a = P' a) →
    piProp R ps acc P = piProp R ps' acc P'
  | [], [], acc, P, P', _, hP => by simp only [piProp]; exact hP acc (by simp)
  | [], _ :: _, _, _, _, h, _ => absurd h.1 (by simp)
  | _ :: _, [], _, _, _, h, _ => absurd h.1 (by simp)
  | p :: ps, p' :: ps', acc, P, P', h, hP => by
    obtain ⟨-, hd⟩ := h.head
    simp only [piProp]
    rw [hd acc rfl]
    exact forall_congr fun a => piProp_congr R ps ps' _ P P' (by simpa using h.tail) fun x hx =>
      hP x (by simp at hx ⊢; omega)

/-- `PiOk` reads each domain, and the codomain, at the right number of arguments. -/
theorem piOk_congr (R : DataRead) : ∀ (ps ps' : List PiDom) (acc : List Sem) (out out' : PiCod),
    DomAgree acc.length ps ps' → CodAgree (acc.length + ps.length) out out' →
    PiOk R ps acc out = PiOk R ps' acc out'
  | [], [], acc, out, out', _, hc => by simp only [PiOk]; rw [hc.2 acc (by simp)]
  | [], _ :: _, _, _, _, h, _ => absurd h.1 (by simp)
  | _ :: _, [], _, _, _, h, _ => absurd h.1 (by simp)
  | p :: ps, p' :: ps', acc, out, out', h, hc => by
    obtain ⟨-, hd⟩ := h.head
    simp only [PiOk]
    rw [hd acc rfl]
    congr 1
    exact forall_congr fun a => by
      rw [piOk_congr R ps ps' _ out out' (by simpa using h.tail) ⟨hc.1, fun x hx => hc.2 x (by simp at hx ⊢; omega)⟩]

theorem piTyAt_congr (R : DataRead) (l : Nat) (ps ps' : List PiDom) (out out' : PiCod)
    (h : DomAgree 0 ps ps') (hc : CodAgree ps.length out out') : piTyAt R l ps out = piTyAt R l ps' out' := by
  have hc' : CodAgree (([] : List Sem).length + ps.length) out out' := by simpa using hc
  match l with
  | 0 =>
    simp only [piTyAt]
    congr 1
    refine piProp_congr R ps ps' [] _ _ h fun a ha => ?_
    rw [hc.1, hc.2 a (by simpa using ha)]
  | 1 => simp only [piTyAt]; rw [telL_congr _ ps ps' [] PUnit out out' h hc']
  | 2 => simp only [piTyAt]; rw [telL_congr _ ps ps' [] PUnit out out' h hc']
  | 3 => simp only [piTyAt]; rw [telL_congr _ ps ps' [] PUnit out out' h hc']
  | n + 4 => unfold piTyAt; rfl

theorem closureAt_congr' (R : DataRead) (l : Nat) (φ : Future) (ps ps' : List PiDom) (out out' : PiCod)
    (g g' : List Sem → Option BodyOut) (h : DomAgree 0 ps ps') (hc : CodAgree ps.length out out')
    (hg : ∀ a : List Sem, a.length = ps.length → g a = g' a) :
    closureAt R l φ ps out g = closureAt R l φ ps' out' g' := by
  have hc' : CodAgree (([] : List Sem).length + ps.length) out out' := by simpa using hc
  have hl : ps'.length = ps.length := h.1.symm
  have hg' : ∀ a : List Sem, a.length = ([] : List Sem).length + ps'.length → g a = g' a := fun a ha =>
    hg a (by simpa [hl] using ha)
  match l with
  | 0 => simp only [closureAt]
  | 1 =>
    simp only [closureAt, closureL]
    rw [telL_congr _ ps ps' [] PUnit out out' h hc', mkTelL_g_congr _ φ _ _ (telL_ar _ ps' [] PUnit out') [] _ g g' hg']
  | 2 =>
    simp only [closureAt, closureL]
    rw [telL_congr _ ps ps' [] PUnit out out' h hc', mkTelL_g_congr _ φ _ _ (telL_ar _ ps' [] PUnit out') [] _ g g' hg']
  | 3 =>
    simp only [closureAt, closureL]
    rw [telL_congr _ ps ps' [] PUnit out out' h hc', mkTelL_g_congr _ φ _ _ (telL_ar _ ps' [] PUnit out') [] _ g g' hg']
  | n + 4 => unfold closureAt; rfl

/-! ## A Π's parameter binders -/

/-- Two lists of parameter binders agree, `n` arguments in: the same readings, and each type at the
right number of arguments. -/
def BAgree (n : Nat) (bs bs' : List PBind) : Prop :=
  bs.length = bs'.length ∧ ∀ (i : Nat) (b b' : PBind), bs[i]? = some b → bs'[i]? = some b' →
    b.2 = b'.2 ∧ ∀ acc : List Sem, acc.length = n + i → b.1 acc = b'.1 acc

theorem BAgree.refl (n : Nat) (bs : List PBind) : BAgree n bs bs :=
  ⟨rfl, fun _ b b' h h' => by rw [h] at h'; cases h'; exact ⟨rfl, fun _ _ => rfl⟩⟩

theorem BAgree.snoc {n : Nat} {bs bs' : List PBind} {b b' : PBind} (h : BAgree n bs bs') (he : b.2 = b'.2)
    (hb : ∀ acc : List Sem, acc.length = n + bs.length → b.1 acc = b'.1 acc) : BAgree n (bs ++ [b]) (bs' ++ [b']) := by
  refine ⟨by simp [h.1], fun i c c' hc hc' => ?_⟩
  rw [List.getElem?_append] at hc hc'
  by_cases hi : i < bs.length
  · have hi' : i < bs'.length := h.1 ▸ hi
    simp only [hi, hi', if_true] at hc hc'
    exact h.2 i c c' (by simpa using hc) (by simpa using hc')
  · have hi' : ¬ i < bs'.length := h.1 ▸ hi
    simp only [hi, hi', if_false] at hc hc'
    rw [← h.1] at hc'
    by_cases e : i - bs.length = 0
    · simp only [e, List.getElem?_cons_zero, Option.some.injEq] at hc hc'
      subst hc hc'
      exact ⟨he, fun acc ha => hb acc (by omega)⟩
    · simp [List.getElem?_cons, e] at hc

theorem BAgree.tail {n : Nat} {b b' : PBind} {bs bs' : List PBind} (h : BAgree n (b :: bs) (b' :: bs')) :
    BAgree (n + 1) bs bs' := by
  refine ⟨by simpa using h.1, fun i c c' hc hc' => ?_⟩
  obtain ⟨hd, hty⟩ := h.2 (i + 1) c c' (by simpa using hc) (by simpa using hc')
  exact ⟨hd, fun acc ha => hty acc (by omega)⟩

theorem extendBinds_agree {bs bs' : List PBind} (h : BAgree 0 bs bs') (acc : List Sem) :
    extendBinds bs acc = extendBinds bs' acc := by
  unfold extendBinds
  refine List.map_congr_left fun ai hai => ?_
  obtain ⟨hlt, -⟩ := List.mem_zipIdx' hai
  cases hb : bs[ai.2]? with
  | none =>
    have : bs'[ai.2]? = none := by
      rw [List.getElem?_eq_none_iff] at hb ⊢; rw [← h.1]; exact hb
    rw [this]
  | some b =>
    obtain ⟨b', hb'⟩ : ∃ b', bs'[ai.2]? = some b' := by
      have : ai.2 < bs'.length := by
        rw [← h.1]; exact (List.getElem?_eq_some_iff.1 hb).1
      exact ⟨_, List.getElem?_eq_getElem this⟩
    rw [hb']
    obtain ⟨hd, hty⟩ := h.2 ai.2 b b' hb hb'
    dsimp only
    rw [hd, hty (acc.take ai.2) (by simp; omega)]

theorem extendBy_agree {bs bs' : List PBind} (h : BAgree 0 bs bs') (s : SState) (acc : List Sem) :
    extendBy s bs acc = extendBy s bs' acc := by
  unfold extendBy; rw [extendBinds_agree h]

theorem psOf_length : ∀ (bs : List PBind) (ds : List Term), bs.length = ds.length → (psOf bs ds).length = ds.length
  | [], [], _ => rfl
  | b :: bs, d :: ds, h => by simp [psOf, psOf_length bs ds (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem psOf_agree : ∀ {n : Nat} {bs bs' : List PBind}, BAgree n bs bs' → ∀ (ds : List Term),
    DomAgree n (psOf bs ds) (psOf bs' ds)
  | _, [], [], _, ds => by cases ds <;> exact DomAgree.refl _ _
  | _, [], _ :: _, h, _ => absurd h.1 (by simp)
  | _, _ :: _, [], h, _ => absurd h.1 (by simp)
  | _, b :: bs, b' :: bs', _, [] => DomAgree.refl _ _
  | n, b :: bs, b' :: bs', h, d :: ds => by
    have ih := psOf_agree h.tail ds
    obtain ⟨-, hty⟩ := h.2 0 b b' rfl rfl
    refine ⟨by simp [psOf, ih.1], fun i p p' hp hp' => ?_⟩
    cases i with
    | zero =>
      simp only [psOf, List.getElem?_cons_zero, Option.some.injEq] at hp hp'
      subst hp hp'
      exact ⟨rfl, fun acc ha => by simp only; rw [hty acc (by omega)]⟩
    | succ i =>
      simp only [psOf, List.getElem?_cons_succ] at hp hp'
      obtain ⟨hr, hd⟩ := ih.2 i p p' hp hp'
      exact ⟨hr, fun acc ha => hd acc (by omega)⟩

end Ochr.Meaning.DataModel.Exists.FrameLocal
