import Ir.Noninterference

/-!
# Static checker

`safe` claims a set of agents is unreachable. `Closed` checks the claim is an invariant
of the flow rules over finite universes, so it is decidable. `closed_sound` proves that a
closed claim implies noninterference, so any tool may compute `safe` and Lean checks it.
-/

set_option linter.unusedSectionVars false

namespace Ir

/-- The finite universe of a case study. Its lists, and proofs that they list everything. -/
structure Universe (Agent Board Var : Type) where
  agents : List Agent
  boards : List Board
  vars : List Var
  hA : ∀ a, a ∈ agents
  hB : ∀ b, b ∈ boards
  hV : ∀ v, v ∈ vars

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]

/-- Every agent claimed safe is untouched by each flow rule. -/
def Closed (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (U : Universe Agent Board Var) (safe : Agent → Bool) : Prop :=
  let agents := U.agents; let boards := U.boards; let vars := U.vars
  ∀ y ∈ agents, safe y = true →
    A.controls y = false ∧
    (∀ b ∈ boards, ¬ (A.injects b = true ∧ cfg.reader b y = true)) ∧
    (∀ b ∈ boards, cfg.reader b y = true → ∀ x ∈ agents, cfg.writer b x = true →
      safe x = true) ∧
    (∀ v ∈ vars, cfg.sees y v = true → safe (cfg.owner v) = true) ∧
    ((∀ v ∈ vars, cfg.echoSees v = true → safe (cfg.owner v) = true) ∨
      ∀ b ∈ boards, cfg.reader b y = true → ∀ w ∈ vars, cfg.writer b (cfg.owner w) = false)

instance (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (U : Universe Agent Board Var) (safe : Agent → Bool) :
    Decidable (Closed cfg A U safe) := by
  unfold Closed; infer_instance

theorem closed_sound {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {safe : Agent → Bool} {x : Agent} (U : Universe Agent Board Var)
    (hc : Closed cfg A U safe) (hr : Reach cfg A x) :
    safe x = false := by
  have hA := U.hA; have hB := U.hB; have hV := U.hV
  induction hr with
  | ctrl h =>
    apply Bool.eq_false_iff.2; intro hs
    have := (hc _ (hA _) hs).1; simp_all
  | inj hi hm =>
    apply Bool.eq_false_iff.2; intro hs
    exact (hc _ (hA _) hs).2.1 _ (hB _) ⟨hi, hm⟩
  | board _ hmx hmy ih =>
    apply Bool.eq_false_iff.2; intro hs
    have := (hc _ (hA _) hs).2.2.1 _ (hB _) hmy _ (hA _) hmx; simp_all
  | sees _ hsv ih =>
    apply Bool.eq_false_iff.2; intro hs
    have := (hc _ (hA _) hs).2.2.2.1 _ (hV _) hsv; simp_all
  | @echo v w b y _ he hmw hmy ih =>
    apply Bool.eq_false_iff.2; intro hs
    rcases (hc _ (hA _) hs).2.2.2.2 with hall | hb
    · have := hall v (hV v) he; rw [ih] at this; exact Bool.false_ne_true this
    · have := hb b (hB b) hmy w (hV w); rw [this] at hmw; exact Bool.false_ne_true hmw

/-- Noninterference from a checked certificate. If the check passes and `a` is claimed safe,
`a` acts the same under any two attacker attacks. -/
theorem noninterference_of_closed {cfg : Config Agent Board Var Val Msg}
    {A : Adversary Agent Board} {safe : Agent → Bool} {a : Agent}
    {honest : Behaviour Agent Board Var Val Msg} {adv₁ adv₂ : Attack Agent Board Var Val Msg}
    {s₀ : State Agent Board Var Val Msg} {sched : List (Turn Agent)}
    (U : Universe Agent Board Var) (hc : Closed cfg A U safe) (ha : safe a = true) :
    actionsOf cfg A honest adv₁ a sched s₀ = actionsOf cfg A honest adv₂ a sched s₀ :=
  noninterference honest adv₁ adv₂ s₀ sched a fun hr => by
    simp [closed_sound U hc hr] at ha

/-- Unverified fixpoint computing reachable agents. `Closed` checks its output. -/
def reachable (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (U : Universe Agent Board Var) : List Agent :=
  let agents := U.agents; let boards := U.boards; let vars := U.vars
  let init := agents.filter fun x =>
    A.controls x || boards.any fun b => A.injects b && cfg.reader b x
  let next (R : List Agent) : List Agent := agents.filter fun y =>
    R.contains y ||
    R.any (fun x => boards.any fun b => cfg.writer b x && cfg.reader b y) ||
    vars.any (fun v => R.contains (cfg.owner v) && cfg.sees y v) ||
    (vars.any (fun v => R.contains (cfg.owner v) && cfg.echoSees v) &&
      boards.any fun b => cfg.reader b y && vars.any fun w => cfg.writer b (cfg.owner w))
  (List.range agents.length).foldl (fun R _ => next R) init

def safeOf (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (U : Universe Agent Board Var) (a : Agent) : Bool :=
  !(reachable cfg A U).contains a

end Ir
