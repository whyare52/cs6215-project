import Ir.Basic

/-!
# Availability

Context overflow is bounded by fan-in. A board grows by at most one entry per action of one
of its writers, so if every turn takes at most `k` actions, by at most `k` per writer turn.
A `replace` leaves at most one entry, so it counts as one action like a post.
An agent's prompt grows only with the turns of agents sharing its boards. With one action
per turn, `k = 1`.
-/

set_option linter.unusedSectionVars false

namespace Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
  {honest : Behaviour Agent Board Var Val Msg} {adv : Attack Agent Board Var Val Msg}

/-- Turns that may write board `b`. Its writers, and SYS when `b` is injectable. -/
def writes (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board) (b : Board) :
    Turn Agent → Bool
  | .agent x => cfg.writer b x
  | .sys => A.injects b

theorem post_length (b b' : Board) (e : Option Agent × Msg)
    (s : State Agent Board Var Val Msg) :
    ((post b' e s).logs b).length ≤ (s.logs b).length + (if b = b' then 1 else 0) := by
  simp only [post]
  split <;> simp_all

/-- One action grows board `b` by at most one entry, and only if its agent writes `b`. -/
theorem perform_length (x : Agent) (act : Action Board Var Val Msg) (b : Board)
    (s : State Agent Board Var Val Msg) :
    ((perform cfg x act s).logs b).length ≤ (s.logs b).length + (cfg.writer b x).toNat := by
  cases act with
  | post b' m =>
    simp only [perform]
    split
    · rename_i hm
      refine Nat.le_trans (post_length b b' _ s) ?_
      by_cases hb : b = b'
      · subst hb; simp [hm]
      · simp [hb]
    · simp
  | replace b' m =>
    simp only [perform]
    split
    · rename_i hm
      simp only [setLog]
      split
      · subst_vars; cases m <;> simp [hm]
      · simp
    · simp
  | attend v t =>
    simp only [perform]
    split
    · simp only [commit]
      split <;> simp_all
    · simp
  | skip => exact Nat.le_add_right _ _

theorem performAll_length (x : Agent) (b : Board) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      ((performAll cfg x acts s).logs b).length ≤
        (s.logs b).length + acts.length * (cfg.writer b x).toNat
  | [], _ => by simp [performAll]
  | act :: acts, s => by
    simp only [performAll, List.length_cons, Nat.succ_mul]
    have h₁ := perform_length (cfg := cfg) x act b s
    have h₂ := performAll_length x b acts (perform cfg x act s)
    omega

/-- With at most `k` actions per turn, a turn grows `b` by at most `k` if it writes `b`. -/
theorem step_length {k : Nat} (hk : ∀ x n s, (choose cfg A honest adv n x s).length ≤ k)
    (hk₁ : 1 ≤ k) (n : Nat) (t : Turn Agent) (b : Board)
    (s : State Agent Board Var Val Msg) :
    ((step cfg A honest adv n t s).logs b).length ≤
      (s.logs b).length + k * (writes cfg A b t).toNat := by
  cases t with
  | agent x =>
    simp only [step, writes]
    refine Nat.le_trans (performAll_length x b _ s) ?_
    have := Nat.mul_le_mul_right (cfg.writer b x).toNat (hk x n s)
    omega
  | sys =>
    refine Nat.le_trans (m := (s.logs b).length + (writes cfg A b .sys).toNat) ?_ ?_
    · simp only [step, sysStep, writes]
      split
      · split
        · rename_i hi
          refine Nat.le_trans (post_length b _ _ s) ?_
          split
          · subst_vars; simp [hi]
          · simp
        · simp
      · simp
    · have := Nat.mul_le_mul_right (writes cfg A b .sys).toNat hk₁
      omega

/-- Board `b` grows by at most `k` times the number of its writers' turns. -/
theorem run_length {k : Nat} (hk : ∀ x n s, (choose cfg A honest adv n x s).length ≤ k)
    (hk₁ : 1 ≤ k) (b : Board) (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      ((run cfg A honest adv sched s n).logs b).length ≤
        (s.logs b).length + k * (sched.filter (writes cfg A b)).length := by
  induction sched with
  | nil => intros; simp [run]
  | cons t ts ih =>
    intro n s
    simp only [run]
    refine Nat.le_trans (ih (n := n + 1)) ?_
    have := step_length hk hk₁ n t b s
    cases hw : writes cfg A b t <;> simp_all [Nat.mul_add] <;> omega

/-- Turns by honest writers of `b`. -/
def honestWrites (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (b : Board) : Turn Agent → Bool
  | .agent x => cfg.writer b x && !A.controls x
  | .sys => false

/-- A board with no adversarial writer is bounded by honest turns alone. -/
theorem run_length_honest {k : Nat} (hk : ∀ x n s, (choose cfg A honest adv n x s).length ≤ k)
    (hk₁ : 1 ≤ k) (b : Board) (sched : List (Turn Agent))
    (hb : ∀ t ∈ sched, writes cfg A b t = true → ∃ x, t = .agent x ∧ A.controls x = false)
    {n : Nat} {s : State Agent Board Var Val Msg} :
    ((run cfg A honest adv sched s n).logs b).length ≤
      (s.logs b).length + k * (sched.filter (honestWrites cfg A b)).length := by
  have hf : sched.filter (writes cfg A b) = sched.filter (honestWrites cfg A b) := by
    apply List.filter_congr
    intro t ht
    cases hw : writes cfg A b t
    · cases t <;> simp_all [writes, honestWrites]
    · obtain ⟨x, rfl, hx⟩ := hb t ht hw
      simp_all [writes, honestWrites]
  rw [← hf]
  exact run_length hk hk₁ b sched

end Ir
