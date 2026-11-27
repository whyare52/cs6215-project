import Ir.Noninterference

/-!
# Protocol conformance

Terrarium's phases are advisory, so an agent can post in the execution phase.
A monitor on tool dispatch replaces a disallowed action with `skip`.
Monitored runs conform, and monitoring preserves noninterference, since the monitor
is per-agent and reads only the turn index.
-/

set_option linter.unusedSectionVars false

namespace Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}

inductive Phase where
  | planning
  | execution
  deriving DecidableEq

/-- Terrarium's discipline. Write boards while planning, commit while executing. A replace
writes a board, so it follows the post rule. -/
def phaseAllowed (phase : Nat → Phase) (n : Nat) : Action Board Var Val Msg → Bool
  | .post _ _ => phase n == .planning
  | .replace _ _ => phase n == .planning
  | .attend _ _ => phase n == .execution
  | .skip => true

def filterAct (allowed : Nat → Action Board Var Val Msg → Bool) (n : Nat)
    (act : Action Board Var Val Msg) : Action Board Var Val Msg :=
  if allowed n act then act else .skip

def monitorBehaviour (allowed : Nat → Action Board Var Val Msg → Bool)
    (π : Behaviour Agent Board Var Val Msg) : Behaviour Agent Board Var Val Msg :=
  fun x n s => (π x n s).map (filterAct allowed n)

/-- The adversary's agents go through the same dispatch. SYS posts bypass it. -/
def monitorAttack (allowed : Nat → Action Board Var Val Msg → Bool)
    (adv : Attack Agent Board Var Val Msg) : Attack Agent Board Var Val Msg :=
  ⟨fun x n s => (adv.act x n s).map (filterAct allowed n), adv.inject⟩

/-- Every action chosen along a run, with its turn index and agent. -/
def trace (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (n : Nat) :
    List (Turn Agent) → State Agent Board Var Val Msg →
    List (Nat × Agent × Action Board Var Val Msg)
  | [], _ => []
  | t :: ts, s =>
    (match t with
      | .agent x => (choose cfg A honest adv n x s).map fun act => (n, x, act)
      | .sys => []) ++
    trace cfg A honest adv (n + 1) ts (step cfg A honest adv n t s)

theorem filterAct_allowed {allowed : Nat → Action Board Var Val Msg → Bool}
    (hskip : ∀ n, allowed n .skip = true) (n : Nat) (act : Action Board Var Val Msg) :
    allowed n (filterAct allowed n act) = true := by
  unfold filterAct; split <;> simp_all

/-- Safety. Every action in a monitored run is allowed at its turn. -/
theorem monitored_conforms {allowed : Nat → Action Board Var Val Msg → Bool}
    (hskip : ∀ n, allowed n .skip = true)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      ∀ e ∈ trace cfg A (monitorBehaviour allowed honest) (monitorAttack allowed adv) n sched s,
        allowed e.1 e.2.2 = true := by
  induction sched with
  | nil => intro _ _ e he; simp [trace] at he
  | cons t ts ih =>
    intro n s e he
    simp only [trace, List.mem_append] at he
    rcases he with he | he
    · cases t with
      | agent x =>
        simp only [choose, monitorBehaviour, monitorAttack] at he
        split at he <;>
        · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 he
          obtain ⟨act, -, rfl⟩ := List.mem_map.1 ha'
          exact filterAct_allowed hskip _ _
      | sys => simp at he
    · exact ih e he

/-- Monitoring keeps noninterference. -/
theorem monitored_noninterference (allowed : Nat → Action Board Var Val Msg → Bool)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (s₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (a : Agent)
    (ha : ¬ Reach cfg A a) :
    actionsOf cfg A (monitorBehaviour allowed honest) (monitorAttack allowed adv₁) a sched s₀ =
      actionsOf cfg A (monitorBehaviour allowed honest) (monitorAttack allowed adv₂) a sched s₀ :=
  noninterference _ _ _ s₀ sched a ha

theorem phaseAllowed_skip (phase : Nat → Phase) (n : Nat) :
    phaseAllowed (Board := Board) (Var := Var) (Val := Val) (Msg := Msg) phase n .skip = true :=
  rfl

/-- Under Terrarium's phases, a monitored run never posts while executing. -/
theorem no_post_in_execution (phase : Nat → Phase)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (sched : List (Turn Agent)) {n : Nat} {s : State Agent Board Var Val Msg}
    {k : Nat} {x : Agent} {b : Board} {m : Msg}
    (he : (k, x, Action.post b m) ∈
      trace cfg A (monitorBehaviour (phaseAllowed phase) honest)
        (monitorAttack (phaseAllowed phase) adv) n sched s) :
    phase k = .planning := by
  have := monitored_conforms (phaseAllowed_skip phase) honest adv sched _ he
  simpa [phaseAllowed] using this

end Ir
