import Ir.Basic

/-!
# Ordering

Only a variable's owner can write it. So if the owner has had no turn yet, the variable
still holds its initial value, whatever every agent and the adversary do.
-/

set_option linter.unusedSectionVars false

namespace Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)

/-- A turn by anyone but the owner leaves the variable alone. -/
theorem perform_assign {x : Agent} {v : Var} (hx : x ≠ cfg.owner v)
    (act : Action Board Var Val Msg) (s : State Agent Board Var Val Msg) :
    (perform cfg x act s).assign v = s.assign v := by
  cases act with
  | post b m => simp only [perform]; split <;> rfl
  | replace b m => simp only [perform]; split <;> rfl
  | attend w t =>
    simp only [perform]
    split
    · rename_i h
      have hw : v ≠ w := fun hvw => hx (hvw ▸ h.1.symm)
      simp [commit, hw]
    · rfl
  | skip => rfl

theorem performAll_assign {x : Agent} {v : Var} (hx : x ≠ cfg.owner v) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      (performAll cfg x acts s).assign v = s.assign v
  | [], _ => rfl
  | act :: acts, s => by
    simp only [performAll]
    rw [performAll_assign hx acts, perform_assign cfg hx act s]

/-- SYS only appends to boards. -/
theorem sysStep_assign (n : Nat) (v : Var) (s : State Agent Board Var Val Msg) :
    (sysStep A adv n s).assign v = s.assign v := by
  simp only [sysStep]
  split
  · split <;> rfl
  · rfl

/-- Before the owner's first turn, the variable keeps its initial value. -/
theorem run_assign {v : Var} :
    ∀ (ts : List (Turn Agent)) (n : Nat) (s : State Agent Board Var Val Msg),
      Turn.agent (cfg.owner v) ∉ ts → (run cfg A honest adv ts s n).assign v = s.assign v
  | [], _, _, _ => rfl
  | t :: ts, n, s, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [run]
    rw [run_assign ts (n + 1) _ h.2]
    cases t with
    | agent x =>
      exact performAll_assign cfg (fun hx => h.1 (hx ▸ rfl)) _ s
    | sys => exact sysStep_assign A adv n v s

end Ir
