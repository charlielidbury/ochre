import Ochr.Meaning.Steps.Machine.NoStuck

/-!
# `I`'s body run in a callee frame never ends stuck (machine8; for `CallJInv`)

The wrappers `located` and `noteValue` end stuck only where the run they wrap does; the untyped,
unwanted read of a variable holding a number never does (`nsAt_readPlace_num`); `S(u)` only where
`u`'s evaluation does. So the untyped `eval` of `S(#0)` from any state whose `#0` holds a number never
ends stuck.
-/

namespace Ochr.Meaning.Steps.Machine

open Ochr Ochr.Meaning Ochr.Meaning.Steps Ochr.Meaning.DecideScope Ochr.Meaning.Steps.Slice
open Ochr.Meaning.Steps.Form

theorem nsAt_locateErrors {α : Type} {l : Loc} {x : M α} {s : MState} (hx : NSAt x s) : NSAt (locateErrors l x) s := by
  intro f lg on f' l' h
  unfold locateErrors tryCatchThe at h
  erw [DecideScope.runAll_tryCatch] at h
  revert h
  rcases e : runAll x s f lg with ⟨⟨e₁ | e₁ | ⟨a, s₁⟩, f₁⟩, l₁⟩
  · intro h; cases h
  · intro h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact hx f lg on _ _ e
  · intro h; cases h

theorem nsAt_atLoc {α : Type} {l : Option Loc} {x : M α} {s : MState} (hx : NSAt x s) : NSAt (atLoc l x) s := by
  unfold atLoc; split
  · exact hx
  · exact nsAt_locateErrors hx

theorem ns_noteStateAt (l : Option Loc) (e : Bool) (v : Option (Value × Option Value)) : NS (noteStateAt l e v) := by
  unfold noteStateAt; ns_go2

theorem nsAt_log_bind {β : Type} {g : Array LogEntry → Array LogEntry} {k : PUnit → M β} {s : MState}
    (hk : NSAt (k ()) s) : NSAt (modifyThe (Array LogEntry) g >>= k) s := by
  intro f l on f' l' h
  exact hk f (g l) on f' l' h

theorem nsAt_noteStateAt_bind {β : Type} {l : Option Loc} {e : Bool} {v : Option (Value × Option Value)}
    {k : PUnit → M β} {s : MState} (hk : NSAt (k ()) s) : NSAt (noteStateAt l e v >>= k) s := by
  unfold noteStateAt
  simp only [bind_assoc]
  refine nsAt_get_bind ?_
  split
  · split
    · exact nsAt_log_bind hk
    · simpa only [pure_bind] using hk
  · simpa only [pure_bind] using hk

theorem nsAt_set_bind {β : Type} {s₀ : MState} {k : PUnit → M β} {s : MState} (hk : NSAt (k ()) s₀) :
    NSAt (set s₀ >>= k) s := hk

theorem nsAt_noteValue {t : Term} {x : M (Value × Option Value)} {s : MState} (hx : NSAt x s) :
    NSAt (noteValue t x) s := by
  unfold noteValue
  refine nsAt_bind hx fun _ _ _ _ => NSAt.of_ns ?_ _
  ns_go2
  all_goals first | (unfold noteLoc; ns_go2) | skip

set_option maxHeartbeats 4000000 in
theorem nsAt_evalCore_varNum {n i f j : Nat} {bd : Binding} {hint : Option Value} {s : MState}
    (hn : NumAt s i f j bd) (hw : s.wantHere = false) :
    NSAt (Ochr.evalCore n false (.place (.var i)) hint) s := by
  cases n with
  | zero => unfold Ochr.evalCore; exact ns_exhausted _ _
  | succ k =>
    unfold Ochr.evalCore
    refine nsAt_bind (ns_tick _) fun _ _ s₁ h₁ => ?_
    have hs₁ : s₁ = s := by
      have h₁' : Runs (tick >>= fun _ => (pure () : M Unit)) s ‹_› () s₁ := by rw [bind_pure]; exact h₁
      obtain ⟨_, h'⟩ := Runs.tick_bind h₁'
      exact (runs_pure_inv h').2
    subst hs₁
    refine nsAt_get_bind (nsAt_bind (ns_wanted _) fun _ w s₂ hw' => ?_)
    obtain ⟨rfl, rfl⟩ := runs_wanted_inv hw'
    simp only [Term.placeOperand?]
    refine nsAt_bind (NSAt.of_ns ?_ _) fun _ o s₃ hp => ?_
    · cases k with
      | zero => unfold projIn; exact ns_exhausted _
      | succ k => unfold projIn; exact ns_pure _
    obtain ⟨rfl, rfl⟩ := runs_projIn_var hp
    simp only [hw, Bool.false_eq_true, if_false]
    refine nsAt_bind (ns_pure _ _) fun _ _ s₄ h₄ => ?_
    obtain ⟨rfl, rfl⟩ := runs_pure_inv h₄
    exact nsAt_bind (nsAt_readPlace_num hn) fun _ _ _ _ => ns_pure _ _

end Ochr.Meaning.Steps.Machine
