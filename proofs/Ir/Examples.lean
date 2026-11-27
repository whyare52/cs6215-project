import Ir.Check
import Ir.Confidentiality

/-!
# Meeting scheduling, Terrarium versus hardened

Agents are Alice 0, Bob 1, Carol 2 and Mallory 3, with Mallory adversarial.
Board 0 holds Alice and Bob, board 1 holds Carol and Mallory.
Each agent owns the variable with its own index.
-/

namespace Ir.Examples

abbrev Ag := Fin 4
abbrev Bd := Fin 2
abbrev Vr := Fin 4

def agents : List Ag := [0, 1, 2, 3]
def boards : List Bd := [0, 1]
def vars : List Vr := [0, 1, 2, 3]

def world : Universe Ag Bd Vr where
  agents := agents
  boards := boards
  vars := vars
  hA := by decide
  hB := by decide
  hV := by decide

def member (b : Bd) (a : Ag) : Bool :=
  (b == 0 && (a == 0 || a == 1)) || (b == 1 && (a == 2 || a == 3))

def mallory : Adversary Ag Bd where
  controls a := a == 3
  injects _ := false

/-- Terrarium as shipped. Full assignment in every prompt and in every echo. -/
def terrarium : Config Ag Bd Vr Nat String where
  reader := member
  owner v := v
  sees _ _ := true
  echoSees _ := true
  echo _ := "action_executed"

/-- Each agent sees only its own variable, and echoes carry no assignment. -/
def hardened : Config Ag Bd Vr Nat String :=
  { terrarium with sees := fun a v => a == v, echoSees := fun _ => false }

/-- In Terrarium, Mallory's commit shows up in Alice's prompt. -/
theorem terrarium_alice_reached : Reach terrarium mallory 0 :=
  Reach.sees (v := 3) (Reach.ctrl rfl) rfl

/-- The fixpoint finds Mallory and Carol only. -/
example : reachable hardened mallory world = [2, 3] := by decide

theorem hardened_closed :
    Closed hardened mallory world (safeOf hardened mallory world) := by
  decide

/-- Alice acts identically whatever Mallory does. -/
theorem hardened_alice_ni (honest : Behaviour Ag Bd Vr Nat String)
    (adv₁ adv₂ : Attack Ag Bd Vr Nat String) (s₀ : State Ag Bd Vr Nat String)
    (sched : List (Turn Ag)) :
    actionsOf hardened mallory honest adv₁ 0 sched s₀ =
      actionsOf hardened mallory honest adv₂ 0 sched s₀ :=
  noninterference_of_closed (a := 0) world hardened_closed (by decide)

/-- Alice holds a secret. -/
def alice : Ag → Bool := fun a => a == 0

/-- In Terrarium, Alice's commit reaches Mallory's prompt. -/
theorem terrarium_leaks : Reach terrarium (holders alice) 3 :=
  Reach.sees (v := 0) (Reach.ctrl rfl) rfl

theorem hardened_no_leak_closed :
    Closed hardened (holders alice) world
      (safeOf hardened (holders alice) world) := by
  decide

/-- Mallory's views are the same whatever Alice's secret is. -/
theorem hardened_no_leak {Sec : Type}
    (P : Ag → Sec → Nat → State Ag Bd Vr Nat String → List (Action Bd Vr Nat String))
    (σ₁ σ₂ : Ag → Sec) (hσ : ∀ x, alice x = false → σ₁ x = σ₂ x)
    (s₀ : State Ag Bd Vr Nat String) (sched : List (Turn Ag)) :
    viewsOf hardened noAdversary (fun x => P x (σ₁ x)) idle 3 sched s₀ =
      viewsOf hardened noAdversary (fun x => P x (σ₂ x)) idle 3 sched s₀ :=
  no_leak alice P σ₁ σ₂ hσ s₀ sched 3 fun hr => by
    have := closed_sound world hardened_no_leak_closed hr
    revert this; decide

end Ir.Examples
