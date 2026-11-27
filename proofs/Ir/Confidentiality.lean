import Ir.Noninterference

/-!
# Confidentiality

Leakage is reachability from the secret holders. If agent `y` is unreachable from the
agents in `S`, then whatever `S` hold privately, `y` sees the same views in every run.
The proof reduces to integrity, by treating the agents in `S` as the adversary.
-/

set_option linter.unusedSectionVars false

namespace Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg}

/-- The views agent `a` receives along a run, in order. -/
def viewsOf (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (a : Agent) :
    List (Turn Agent) → State Agent Board Var Val Msg → optParam Nat 0 →
    List (State Agent Board Var Val Msg)
  | [], _, _ => []
  | t :: ts, s, n =>
    (match t with
      | .agent x => if x = a then [view cfg a s] else []
      | .sys => []) ++
    viewsOf cfg A honest adv a ts (step cfg A honest adv n t s) (n + 1)

theorem viewsOf_eq {A : Adversary Agent Board} {honest : Behaviour Agent Board Var Val Msg}
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} {a : Agent}
    (ha : ¬ Reach cfg A a) (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s₁ s₂ : State Agent Board Var Val Msg}, Agree cfg A s₁ s₂ →
      viewsOf cfg A honest adv₁ a sched s₁ n = viewsOf cfg A honest adv₂ a sched s₂ n := by
  induction sched with
  | nil => intros; rfl
  | cons t ts ih =>
    intro n s₁ s₂ h
    simp only [viewsOf]
    congr 1
    · cases t with
      | agent x =>
        simp only
        split
        · rw [view_eq h ha]
        · rfl
      | sys => rfl
    · exact ih (agree_step n t h)

/-- `viewsOf` depends only on the transition function. -/
theorem viewsOf_congr {A A' : Adversary Agent Board} {π π' : Behaviour Agent Board Var Val Msg}
    {adv adv' : Attack Agent Board Var Val Msg} {a : Agent}
    (hstep : ∀ n t s, step cfg A π adv n t s = step cfg A' π' adv' n t s)
    (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      viewsOf cfg A π adv a sched s n = viewsOf cfg A' π' adv' a sched s n := by
  induction sched with
  | nil => intros; rfl
  | cons t ts ih =>
    intro n s
    simp only [viewsOf, hstep]
    rw [ih]

/-- No adversary. Every agent runs its behaviour and SYS stays silent. -/
def noAdversary : Adversary Agent Board := ⟨fun _ => false, fun _ => false⟩

def idle : Attack Agent Board Var Val Msg := ⟨fun _ _ _ => [], fun _ _ => none⟩

/-- The agents in `S`, seen as an adversary. -/
def holders (S : Agent → Bool) : Adversary Agent Board := ⟨S, fun _ => false⟩

/-- Run behaviour profile `π` on the agents the adversary controls. -/
def profile (cfg : Config Agent Board Var Val Msg) (π : Behaviour Agent Board Var Val Msg) :
    Attack Agent Board Var Val Msg :=
  ⟨fun x n s => π x n (view cfg x s), fun _ _ => none⟩

theorem step_as_holders {S : Agent → Bool} {π₀ π : Behaviour Agent Board Var Val Msg}
    (hπ : ∀ x, S x = false → π x = π₀ x) (n : Nat) (t : Turn Agent)
    (s : State Agent Board Var Val Msg) :
    step cfg noAdversary π idle n t s = step cfg (holders S) π₀ (profile cfg π) n t s := by
  cases t with
  | agent x =>
    simp only [step, choose, noAdversary, holders, profile, Bool.false_eq_true, ite_false]
    by_cases hx : S x = true
    · simp [hx]
    · simp only [Bool.not_eq_true] at hx
      simp [hx, hπ x hx]
  | sys => simp [step, sysStep, idle, profile]

/-- Confidentiality. Profiles that differ only on `S` give `y` the same views,
whenever `y` is unreachable from `S`. -/
theorem confidentiality (S : Agent → Bool) (π₁ π₂ : Behaviour Agent Board Var Val Msg)
    (hπ : ∀ x, S x = false → π₁ x = π₂ x) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) (y : Agent) (hy : ¬ Reach cfg (holders S) y) :
    viewsOf cfg noAdversary π₁ idle y sched s₀ =
      viewsOf cfg noAdversary π₂ idle y sched s₀ := by
  rw [viewsOf_congr (step_as_holders (π₀ := π₁) (fun _ _ => rfl)),
    viewsOf_congr (step_as_holders (π₀ := π₁) fun x hx => (hπ x hx).symm)]
  exact viewsOf_eq hy sched (Agree.refl s₀)

/-- No leakage of secrets. Each agent's behaviour is parameterised by its own secret. -/
theorem no_leak {Sec : Type} (S : Agent → Bool)
    (P : Agent → Sec → Nat → State Agent Board Var Val Msg →
      List (Action Board Var Val Msg))
    (σ₁ σ₂ : Agent → Sec) (hσ : ∀ x, S x = false → σ₁ x = σ₂ x)
    (s₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (y : Agent)
    (hy : ¬ Reach cfg (holders S) y) :
    viewsOf cfg noAdversary (fun x => P x (σ₁ x)) idle y sched s₀ =
      viewsOf cfg noAdversary (fun x => P x (σ₂ x)) idle y sched s₀ :=
  confidentiality S _ _ (fun x hx => by simp only [hσ x hx]) s₀ sched y hy

end Ir
