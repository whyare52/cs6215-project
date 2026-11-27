import Ir.Contracts
import Ir.Noninterference

/-!
# Noninterference under contracts

A contract reads the full state, so a guard could leak the attacker's influence into an
unreachable agent's move. It cannot if, for every unreachable agent, the verdict depends only
on what `Agree` fixes. Then `runC` keeps `Agree`, as `run` does.
-/

namespace Ir

/-- The contract's verdict on an unreachable agent's action is the same in agreeing states. -/
def RespectsAgree {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (C : Contract Agent Board Var Val Msg) : Prop :=
  ∀ x s₁ s₂ act, ¬ Reach cfg A x → Agree cfg A s₁ s₂ → C x s₁ act = C x s₂ act

/-- A reachable agent's guarded turn changes nothing an unreachable agent can see. -/
theorem agree_performC_reach {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {C : Contract Agent Board Var Val Msg} {x : Agent} (hx : Reach cfg A x) :
    ∀ (acts : List (Action Board Var Val Msg)) {s₁ s₂ : State Agent Board Var Val Msg},
      Agree cfg A s₁ s₂ → Agree cfg A (performC cfg C x acts s₁) s₂
  | [], _, _, h => h
  | _ :: acts, _, _, h => agree_performC_reach hx acts (agree_perform_reach hx h)

/-- An unreachable agent's guarded turn has the same verdicts and effect in both runs. -/
theorem agree_performC_same {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {C : Contract Agent Board Var Val Msg} (hC : RespectsAgree cfg A C) {x : Agent}
    (hx : ¬ Reach cfg A x) :
    ∀ (acts : List (Action Board Var Val Msg)) {s₁ s₂ : State Agent Board Var Val Msg},
      Agree cfg A s₁ s₂ →
      guardAll cfg C x acts s₁ = guardAll cfg C x acts s₂ ∧
        Agree cfg A (performC cfg C x acts s₁) (performC cfg C x acts s₂)
  | [], _, _, h => ⟨rfl, h⟩
  | act :: acts, s₁, s₂, h => by
    have hg : guard C x s₁ act = guard C x s₂ act := by rw [guard, guard, hC x s₁ s₂ act hx h]
    have ih := agree_performC_same hC hx acts (s₁ := perform cfg x (guard C x s₁ act) s₁)
      (s₂ := perform cfg x (guard C x s₂ act) s₂) (by rw [hg]; exact agree_perform_same hx h)
    simp only [guardAll, performC, hg] at ih ⊢
    exact ⟨by rw [ih.1], ih.2⟩

/-- Unwinding for guarded steps. -/
theorem agree_stepC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (hC : RespectsAgree cfg A C) (n : Nat)
    (t : Turn Agent) {s₁ s₂ : State Agent Board Var Val Msg} (h : Agree cfg A s₁ s₂) :
    Agree cfg A (stepC cfg A honest adv₁ C n t s₁) (stepC cfg A honest adv₂ C n t s₂) := by
  cases t with
  | agent x =>
    simp only [stepC]
    by_cases hx : Reach cfg A x
    · exact (agree_performC_reach hx _ (agree_performC_reach hx _ h).symm).symm
    · rw [choose_eq (adv₂ := adv₂) hx h]
      exact (agree_performC_same hC hx _ h).2
  | sys =>
    simp only [stepC]
    exact (agree_sys_left (agree_sys_left h).symm).symm

theorem agree_runC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (hC : RespectsAgree cfg A C) :
    ∀ (sched : List (Turn Agent)) (n : Nat) {s₁ s₂ : State Agent Board Var Val Msg},
      Agree cfg A s₁ s₂ →
      Agree cfg A (runC cfg A honest adv₁ C sched s₁ n) (runC cfg A honest adv₂ C sched s₂ n)
  | [], _, _, _, h => h
  | t :: ts, n, _, _, h =>
    agree_runC cfg A honest adv₁ adv₂ C hC ts (n + 1)
      (agree_stepC cfg A honest adv₁ adv₂ C hC n t h)

/-- The actions agent `a` takes along a guarded run, after the guard, one list per turn. -/
def actionsOfC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (a : Agent) :
    List (Turn Agent) → State Agent Board Var Val Msg → optParam Nat 0 →
    List (List (Action Board Var Val Msg))
  | [], _, _ => []
  | t :: ts, s, n =>
    (match t with
      | .agent x => if x = a then [guardAll cfg C a (choose cfg A honest adv n a s) s] else []
      | .sys => []) ++
    actionsOfC cfg A honest adv C a ts (stepC cfg A honest adv C n t s) (n + 1)

theorem actionsOfC_eq {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (hC : RespectsAgree cfg A C) (a : Agent)
    (ha : ¬ Reach cfg A a) :
    ∀ (sched : List (Turn Agent)) (n : Nat) {s₁ s₂ : State Agent Board Var Val Msg},
      Agree cfg A s₁ s₂ →
      actionsOfC cfg A honest adv₁ C a sched s₁ n = actionsOfC cfg A honest adv₂ C a sched s₂ n
  | [], _, _, _, _ => rfl
  | t :: ts, n, s₁, s₂, h => by
    simp only [actionsOfC]
    congr 1
    · cases t with
      | agent x =>
        simp only
        split
        · rw [choose_eq (adv₂ := adv₂) ha h, (agree_performC_same hC ha _ h).1]
        · rfl
      | sys => rfl
    · exact actionsOfC_eq cfg A honest adv₁ adv₂ C hC a ha ts (n + 1)
        (agree_stepC cfg A honest adv₁ adv₂ C hC n t h)

/-- Without a flow path from the attacker, `a` takes the same guarded actions under any two
attacker attacks, if the contract respects `Agree`. -/
theorem noninterferenceC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (hC : RespectsAgree cfg A C)
    (s₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (a : Agent)
    (ha : ¬ Reach cfg A a) :
    actionsOfC cfg A honest adv₁ C a sched s₀ = actionsOfC cfg A honest adv₂ C a sched s₀ :=
  actionsOfC_eq cfg A honest adv₁ adv₂ C hC a ha sched 0 (Agree.refl s₀)

/-- Variables with an unreachable owner end with the same value in both guarded runs. -/
theorem assign_fixedC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (hC : RespectsAgree cfg A C)
    (s₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (v : Var)
    (hv : ¬ Reach cfg A (cfg.owner v)) :
    (runC cfg A honest adv₁ C sched s₀).assign v =
      (runC cfg A honest adv₂ C sched s₀).assign v :=
  (agree_runC cfg A honest adv₁ adv₂ C hC sched 0 (Agree.refl s₀)).1 v hv

end Ir
