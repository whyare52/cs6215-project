import Ir.Basic

/-!
# Noninterference

If the adversary has no flow path to agent `a`, then changing the adversary's
attack leaves every action of `a` unchanged.
The proof is an unwinding argument. `Agree` is preserved by every transition.
-/

set_option linter.unusedSectionVars false

namespace Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}

/-- Two states agree on every variable with an unreachable owner and on every board
an unreachable agent reads. -/
def Agree (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (s₁ s₂ : State Agent Board Var Val Msg) : Prop :=
  (∀ v, ¬ Reach cfg A (cfg.owner v) → s₁.assign v = s₂.assign v) ∧
    ∀ b u, ¬ Reach cfg A u → cfg.reader b u = true → s₁.logs b = s₂.logs b

theorem Agree.refl (s : State Agent Board Var Val Msg) : Agree cfg A s s :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Agree.symm {s₁ s₂ : State Agent Board Var Val Msg} (h : Agree cfg A s₁ s₂) :
    Agree cfg A s₂ s₁ :=
  ⟨fun v hv => (h.1 v hv).symm, fun b u hu hm => (h.2 b u hu hm).symm⟩

theorem view_eq {a : Agent} {s₁ s₂ : State Agent Board Var Val Msg}
    (h : Agree cfg A s₁ s₂) (ha : ¬ Reach cfg A a) : view cfg a s₁ = view cfg a s₂ := by
  simp only [view, State.mk.injEq]
  refine ⟨funext fun b => ?_, funext fun v => ?_⟩
  · split
    · exact h.2 b a ha (by assumption)
    · rfl
  · split
    · exact h.1 v fun hr => ha (Reach.sees hr (by assumption))
    · rfl

/-- Rewriting a board whose readers are all reachable keeps agreement. -/
theorem agree_setLog_left {b : Board} {l : List (Option Agent × Msg)}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hb : ∀ u, cfg.reader b u = true → Reach cfg A u) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (setLog b l s₁) s₂ := by
  refine ⟨h.1, fun b' u hu hm => ?_⟩
  simp only [setLog]
  split
  · subst_vars; exact absurd (hb u hm) hu
  · exact h.2 b' u hu hm

/-- Posting to a board whose readers are all reachable keeps agreement. -/
theorem agree_post_left {b : Board} {e : Option Agent × Msg}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hb : ∀ u, cfg.reader b u = true → Reach cfg A u) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (post b e s₁) s₂ :=
  agree_setLog_left hb h

/-- Rewriting a board in both runs keeps agreement, if the new logs are equal whenever an
unreachable agent reads the board. Posts and replacements are both of this form. -/
theorem agree_setLog {b : Board} {l₁ l₂ : List (Option Agent × Msg)}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hl : ∀ u, ¬ Reach cfg A u → cfg.reader b u = true → l₁ = l₂) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (setLog b l₁ s₁) (setLog b l₂ s₂) := by
  refine ⟨h.1, fun b' u hu hm => ?_⟩
  simp only [setLog]
  split
  · subst_vars; exact hl u hu hm
  · exact h.2 b' u hu hm

/-- A reachable agent's move changes nothing an unreachable agent can see. -/
theorem agree_perform_reach {x : Agent} {act : Action Board Var Val Msg}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hx : Reach cfg A x) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (perform cfg x act s₁) s₂ := by
  cases act with
  | post b m =>
    simp only [perform]
    split
    · exact agree_post_left (fun u hu => Reach.board hx (by assumption) hu) h
    · exact h
  | replace b m =>
    simp only [perform]
    split
    · exact agree_setLog_left (fun u hu => Reach.board hx (by assumption) hu) h
    · exact h
  | attend v t =>
    simp only [perform]
    split
    · rename_i hc
      have hov : Reach cfg A (cfg.owner v) := by rw [hc.1]; exact hx
      refine ⟨fun v' hv' => ?_, fun b u hu hm => ?_⟩
      · simp only [commit]
        split
        · rename_i heq; rw [heq] at hv'; exact absurd hov hv'
        · exact h.1 v' hv'
      · simp only [commit]
        split
        · exact absurd (Reach.board hx (by assumption) hm) hu
        · exact h.2 b u hu hm
    · exact h
  | skip => exact h

/-- An unreachable agent's commit writes the same value, and echoes the same summary to any
board an unreachable agent reads. -/
theorem agree_commit_same {x : Agent} {v : Var} {t : Val}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (ho : cfg.owner v = x) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (commit cfg x v t s₁) (commit cfg x v t s₂) := by
  refine ⟨fun v' hv' => ?_, fun b u hu hm => ?_⟩
  · simp only [commit]
    split
    · rfl
    · exact h.1 v' hv'
  · simp only [commit]
    split
    · rename_i hbx
      rw [h.2 b u hu hm]
      congr 3
      congr 1
      funext v'
      split
      · split
        · rfl
        · refine h.1 v' fun hr => hu (Reach.echo (w := v) hr (by assumption) ?_ hm)
          rw [ho]; exact hbx
      · rfl
    · exact h.2 b u hu hm

/-- An unreachable agent makes the same move in both runs. -/
theorem agree_perform_same {x : Agent} {act : Action Board Var Val Msg}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hx : ¬ Reach cfg A x) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (perform cfg x act s₁) (perform cfg x act s₂) := by
  cases act with
  | post b m =>
    simp only [perform]
    split
    · exact agree_setLog (fun u hu hm => by rw [h.2 _ u hu hm]) h
    · exact h
  | replace b m =>
    simp only [perform]
    split
    · exact agree_setLog (fun _ _ _ => rfl) h
    · exact h
  | attend v t =>
    by_cases ho : cfg.owner v = x
    · have hv : s₁.assign v = s₂.assign v := h.1 v (by rw [ho]; exact hx)
      simp only [perform, ho, true_and, hv]
      split
      · exact agree_commit_same ho h
      · exact h
    · simp only [perform, ho, false_and, ↓reduceIte]
      exact h
  | skip => exact h

/-- A reachable agent's turn changes nothing an unreachable agent can see. -/
theorem agree_performAll_reach {x : Agent} {acts : List (Action Board Var Val Msg)}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hx : Reach cfg A x) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (performAll cfg x acts s₁) s₂ := by
  induction acts generalizing s₁ with
  | nil => exact h
  | cons act acts ih => exact ih (agree_perform_reach hx h)

/-- An unreachable agent's turn has the same effect in both runs. -/
theorem agree_performAll_same {x : Agent} {acts : List (Action Board Var Val Msg)}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hx : ¬ Reach cfg A x) (h : Agree cfg A s₁ s₂) :
    Agree cfg A (performAll cfg x acts s₁) (performAll cfg x acts s₂) := by
  induction acts generalizing s₁ s₂ with
  | nil => exact h
  | cons act acts ih => exact ih (agree_perform_same hx h)

theorem agree_sys_left {adv : Attack Agent Board Var Val Msg} {n : Nat}
    {s₁ s₂ : State Agent Board Var Val Msg} (h : Agree cfg A s₁ s₂) :
    Agree cfg A (sysStep A adv n s₁) s₂ := by
  unfold sysStep
  split
  · split
    · exact agree_post_left (fun u hu => Reach.inj (by assumption) hu) h
    · exact h
  · exact h

theorem choose_eq {honest : Behaviour Agent Board Var Val Msg}
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} {n : Nat} {x : Agent}
    {s₁ s₂ : State Agent Board Var Val Msg}
    (hx : ¬ Reach cfg A x) (h : Agree cfg A s₁ s₂) :
    choose cfg A honest adv₁ n x s₁ = choose cfg A honest adv₂ n x s₂ := by
  have hc : A.controls x = false := by
    cases hb : A.controls x with
    | false => rfl
    | true => exact absurd (Reach.ctrl hb) hx
  simp only [choose, hc, Bool.false_eq_true, ite_false, view_eq h hx]

/-- Unwinding. Every transition preserves `Agree`. -/
theorem agree_step {honest : Behaviour Agent Board Var Val Msg}
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} (n : Nat) (t : Turn Agent)
    {s₁ s₂ : State Agent Board Var Val Msg} (h : Agree cfg A s₁ s₂) :
    Agree cfg A (step cfg A honest adv₁ n t s₁) (step cfg A honest adv₂ n t s₂) := by
  cases t with
  | agent x =>
    simp only [step]
    by_cases hx : Reach cfg A x
    · exact (agree_performAll_reach hx (agree_performAll_reach hx h).symm).symm
    · rw [choose_eq (adv₂ := adv₂) hx h]
      exact agree_performAll_same hx h
  | sys =>
    simp only [step]
    exact (agree_sys_left (agree_sys_left h).symm).symm

theorem actionsOf_eq {honest : Behaviour Agent Board Var Val Msg}
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} {a : Agent}
    (ha : ¬ Reach cfg A a) (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s₁ s₂ : State Agent Board Var Val Msg}, Agree cfg A s₁ s₂ →
      actionsOf cfg A honest adv₁ a sched s₁ n = actionsOf cfg A honest adv₂ a sched s₂ n := by
  induction sched with
  | nil => intros; rfl
  | cons t ts ih =>
    intro n s₁ s₂ h
    simp only [actionsOf]
    congr 1
    · cases t with
      | agent x =>
        simp only
        split
        · rw [choose_eq ha h]
        · rfl
      | sys => rfl
    · exact ih (agree_step n t h)

/-- Main theorem. Without a flow path from the adversary, `a` acts identically
under any two adversary attacks, for every fixing of the honest randomness. -/
theorem noninterference (honest : Behaviour Agent Board Var Val Msg)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) (a : Agent) (ha : ¬ Reach cfg A a) :
    actionsOf cfg A honest adv₁ a sched s₀ = actionsOf cfg A honest adv₂ a sched s₀ :=
  actionsOf_eq ha sched (Agree.refl s₀)

theorem agree_run {honest : Behaviour Agent Board Var Val Msg}
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s₁ s₂ : State Agent Board Var Val Msg}, Agree cfg A s₁ s₂ →
      Agree cfg A (run cfg A honest adv₁ sched s₁ n) (run cfg A honest adv₂ sched s₂ n) := by
  induction sched with
  | nil => intro _ _ _ h; exact h
  | cons t ts ih => intro n _ _ h; exact ih (agree_step n t h)

/-- Corollary. Variables with an unreachable owner end with the same value. -/
theorem assign_fixed (honest : Behaviour Agent Board Var Val Msg)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) (v : Var) (hv : ¬ Reach cfg A (cfg.owner v)) :
    (run cfg A honest adv₁ sched s₀).assign v = (run cfg A honest adv₂ sched s₀).assign v :=
  (agree_run sched (Agree.refl s₀)).1 v hv

end Ir
