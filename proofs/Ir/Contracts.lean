import Ir.Basic

/-!
# Runtime contracts

A contract is a runtime guard on actions. The monitor reads the full state, and it
replaces any action that breaks the contract with `skip`. It cannot tell who is malicious,
so it guards every agent. Under a contract, theorems can talk about values, not only wiring.
-/

namespace Ir

/-- Whether agent `x` may take an action in state `s`. -/
abbrev Contract (Agent Board Var Val Msg : Type) :=
  Agent → State Agent Board Var Val Msg → Action Board Var Val Msg → Bool

/-- Let the action through if the contract allows it, else skip. -/
def guard {Agent Board Var Val Msg : Type}
    (C : Contract Agent Board Var Val Msg) (x : Agent) (s : State Agent Board Var Val Msg)
    (act : Action Board Var Val Msg) :
    Action Board Var Val Msg :=
  if C x s act then act else .skip

/-- A turn under the contract. Each action is guarded against the state the previous ones
left, and a rejected action is skipped. -/
def performC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg) (x : Agent) :
    List (Action Board Var Val Msg) → State Agent Board Var Val Msg →
    State Agent Board Var Val Msg
  | [], s => s
  | act :: acts, s => performC cfg C x acts (perform cfg x (guard C x s act) s)

/-- The actions a guarded turn performs, each rejected one replaced by `skip`. -/
def guardAll {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg) (x : Agent) :
    List (Action Board Var Val Msg) → State Agent Board Var Val Msg →
    List (Action Board Var Val Msg)
  | [], _ => []
  | act :: acts, s =>
    guard C x s act :: guardAll cfg C x acts (perform cfg x (guard C x s act) s)

/-- A guarded turn is the plain turn that performs its guarded actions. -/
theorem performC_eq {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg) (x : Agent) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      performC cfg C x acts s = performAll cfg x (guardAll cfg C x acts s) s
  | [], _ => rfl
  | _ :: acts, _ => performC_eq cfg C x acts _

/-- Like `step`, but every agent's chosen actions pass the guard. SYS is unchanged. -/
def stepC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (n : Nat) :
    Turn Agent → State Agent Board Var Val Msg → State Agent Board Var Val Msg
  | .agent x, s => performC cfg C x (choose cfg A honest adv n x s) s
  | .sys, s => sysStep A adv n s

/-- Like `run`, under the contract. -/
def runC {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) :
    List (Turn Agent) → State Agent Board Var Val Msg → optParam Nat 0 →
    State Agent Board Var Val Msg
  | [], s, _ => s
  | t :: ts, s, n => runC cfg A honest adv C ts (stepC cfg A honest adv C n t s) (n + 1)

/-- A guarded turn keeps an invariant that allowed actions keep. -/
theorem performC_invariant {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg)
    (I : State Agent Board Var Val Msg → Prop)
    (hact : ∀ x s act, I s → C x s act = true → I (perform cfg x act s)) (x : Agent) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      I s → I (performC cfg C x acts s)
  | [], _, h => h
  | act :: acts, s, h => by
    simp only [performC]
    apply performC_invariant cfg C I hact x acts
    simp only [guard]
    split
    · exact hact x s act h ‹_›
    · exact h

/-- An invariant holds along every guarded run if allowed actions and SYS preserve it.
Skipped actions preserve it for free. -/
theorem runC_invariant {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (I : State Agent Board Var Val Msg → Prop)
    (hact : ∀ x s act, I s → C x s act = true → I (perform cfg x act s))
    (hsys : ∀ n s, I s → I (sysStep A adv n s)) :
    ∀ (sched : List (Turn Agent)) (s₀ : State Agent Board Var Val Msg) (n : Nat),
      I s₀ → I (runC cfg A honest adv C sched s₀ n)
  | [], _, _, h => h
  | t :: ts, s, n, h => by
    simp only [runC]
    apply runC_invariant cfg A honest adv C I hact hsys ts _ (n + 1)
    cases t with
    | agent x => exact performC_invariant cfg C I hact x _ s h
    | sys => exact hsys n s h

end Ir
