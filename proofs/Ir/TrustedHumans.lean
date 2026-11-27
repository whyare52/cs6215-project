import Ir.Completeness
import Ir.Monotone

/-!
# Trusted humans

A human is trusted not to forward the attacker's text: an honest human acts on the turn index
alone, never on what it reads (`Trusting`). Such a human acts the same whether or not it can
read, so trusting humans reduces to the configuration in which an uncontrolled human reads no
board and sees no variable (`Config.trusting`). Every run, action and view of the original
configuration equals the one of the trusting configuration, so `Reach` of the trusting
configuration inherits noninterference and exactness. Taint stops at a trusted human. A human
the attacker controls keeps its reads, since the attacker drives it.
-/

namespace Ir

set_option linter.unusedSectionVars false

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]

/-- The configuration under the trust assumption. An uncontrolled human reads no board and
sees no variable. Writers, owners and the echo are unchanged. -/
def Config.trusting (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (human : Agent → Bool) : Config Agent Board Var Val Msg :=
  { cfg with
    reader := fun b x => cfg.reader b x && (A.controls x || !human x)
    sees := fun x v => cfg.sees x v && (A.controls x || !human x) }

/-- Honest humans act on the turn index alone, never on their view. -/
def Trusting (human : Agent → Bool) (honest : Behaviour Agent Board Var Val Msg) : Prop :=
  ∀ h, human h = true → ∀ n s₁ s₂, honest h n s₁ = honest h n s₂

section

variable (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (human : Agent → Bool)

theorem trusting_writer : (cfg.trusting A human).writer = cfg.writer := rfl
theorem trusting_owner : (cfg.trusting A human).owner = cfg.owner := rfl

theorem perform_trusting (x : Agent) (act : Action Board Var Val Msg)
    (s : State Agent Board Var Val Msg) :
    perform (cfg.trusting A human) x act s = perform cfg x act s := by
  cases act <;> rfl

theorem performAll_trusting (x : Agent) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      performAll (cfg.trusting A human) x acts s = performAll cfg x acts s
  | [], _ => rfl
  | act :: acts, s => by
    simp only [performAll, perform_trusting]
    exact performAll_trusting x acts _

/-- An agent the trust assumption leaves alone keeps its view. -/
theorem view_trusting {x : Agent} (hx : A.controls x = true ∨ human x = false)
    (s : State Agent Board Var Val Msg) :
    view (cfg.trusting A human) x s = view cfg x s := by
  rcases hx with h | h <;> simp [view, Config.trusting, h]

/-- The trusting view of an original view is the trusting view, since it reads less. -/
theorem view_trusting_view (x : Agent) (s : State Agent Board Var Val Msg) :
    view (cfg.trusting A human) x (view cfg x s) = view (cfg.trusting A human) x s := by
  simp only [view, Config.trusting, State.mk.injEq]
  constructor
  · funext b
    by_cases hr : cfg.reader b x = true <;> simp [hr]
  · funext v
    by_cases hs : cfg.sees x v = true <;> simp [hs]

variable {cfg A human} {honest : Behaviour Agent Board Var Val Msg}
  {adv : Attack Agent Board Var Val Msg}

theorem choose_trusting (ht : Trusting human honest) (n : Nat) (x : Agent)
    (s : State Agent Board Var Val Msg) :
    choose (cfg.trusting A human) A honest adv n x s = choose cfg A honest adv n x s := by
  unfold choose
  cases hc : A.controls x
  · simp only [Bool.false_eq_true, ite_false]
    cases hh : human x
    · rw [view_trusting cfg A human (Or.inr hh)]
    · exact ht x hh n _ _
  · rfl

theorem step_trusting (ht : Trusting human honest) (n : Nat) (t : Turn Agent)
    (s : State Agent Board Var Val Msg) :
    step (cfg.trusting A human) A honest adv n t s = step cfg A honest adv n t s := by
  cases t with
  | agent x => simp only [step, choose_trusting ht, performAll_trusting]
  | sys => rfl

theorem run_trusting (ht : Trusting human honest) :
    ∀ (sched : List (Turn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      run (cfg.trusting A human) A honest adv sched s n = run cfg A honest adv sched s n
  | [], _, _ => rfl
  | t :: ts, s, n => by
    simp only [run, step_trusting ht]
    exact run_trusting ht ts _ _

theorem actionsOf_trusting (ht : Trusting human honest) (a : Agent) :
    ∀ (sched : List (Turn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      actionsOf (cfg.trusting A human) A honest adv a sched s n =
        actionsOf cfg A honest adv a sched s n
  | [], _, _ => rfl
  | t :: ts, s, n => by
    simp only [actionsOf, step_trusting ht, choose_trusting ht]
    rw [actionsOf_trusting ht a ts]

theorem viewsOf_trusting (ht : Trusting human honest) {a : Agent}
    (ha : A.controls a = true ∨ human a = false) :
    ∀ (sched : List (Turn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      viewsOf (cfg.trusting A human) A honest adv a sched s n =
        viewsOf cfg A honest adv a sched s n
  | [], _, _ => rfl
  | t :: ts, s, n => by
    simp only [viewsOf, step_trusting ht, view_trusting cfg A human ha]
    rw [viewsOf_trusting ht ha ts]

end

variable {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
  {human : Agent → Bool}

/-- Trusting humans taints no more agents than `Reach` does. -/
theorem reach_trusting_le {x : Agent} (h : Reach (cfg.trusting A human) A x) :
    Reach cfg A x :=
  Reach.mono (cfg' := cfg.trusting A human) (cfg := cfg) (A' := A) (A := A)
    { owner := rfl
      reader := fun b a h => by simp [Config.trusting] at h; exact h.1
      writer := fun _ _ h => h
      sees := fun a v h => by simp [Config.trusting] at h; exact h.1
      echoSees := fun _ h => h }
    { controls := fun _ h => h, injects := fun _ h => h } h

/-- Noninterference with trusted humans. An agent untainted under the trusting configuration
takes the same actions under any two attacker attacks, for every behaviour whose honest humans
ignore what they read. -/
theorem noninterference_trusting {honest : Behaviour Agent Board Var Val Msg}
    (ht : Trusting human honest) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (s₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (a : Agent)
    (ha : ¬ Reach (cfg.trusting A human) A a) :
    actionsOf cfg A honest adv₁ a sched s₀ = actionsOf cfg A honest adv₂ a sched s₀ := by
  exact (actionsOf_trusting (cfg := cfg) (A := A) (adv := adv₁) ht a sched s₀ 0).symm.trans
    ((noninterference (cfg := cfg.trusting A human) (A := A) honest adv₁ adv₂ s₀ sched a ha).trans
      (actionsOf_trusting (cfg := cfg) (A := A) (adv := adv₂) ht a sched s₀ 0))

/-- A variable whose owner is untainted under the trusting configuration ends the same. -/
theorem assign_fixed_trusting {honest : Behaviour Agent Board Var Val Msg}
    (ht : Trusting human honest) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (s₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (v : Var)
    (hv : ¬ Reach (cfg.trusting A human) A (cfg.owner v)) :
    (run cfg A honest adv₁ sched s₀).assign v = (run cfg A honest adv₂ sched s₀).assign v := by
  have h₁ := run_trusting (cfg := cfg) (A := A) (adv := adv₁) ht sched s₀ 0
  have h₂ := run_trusting (cfg := cfg) (A := A) (adv := adv₂) ht sched s₀ 0
  have h := assign_fixed (cfg := cfg.trusting A human) (A := A) honest adv₁ adv₂ s₀ sched v hv
  simpa only [h₁, h₂] using h

/-! ## Exactness -/

section exact

variable (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (human : Agent → Bool)

theorem view_idem (c : Config Agent Board Var Val Msg) (x : Agent)
    (s : State Agent Board Var Val Msg) : view c x (view c x s) = view c x s := by
  simp only [view, State.mk.injEq]
  constructor
  · funext b; by_cases hr : c.reader b x = true <;> simp [hr]
  · funext v; by_cases hs : c.sees x v = true <;> simp [hs]

/-- The state with every board empty and every variable unset. -/
def emptyState : State Agent Board Var Val Msg := ⟨fun _ => [], fun _ => none⟩

/-- An uncontrolled human sees nothing under the trusting configuration. -/
theorem view_trusting_human {x : Agent} (hc : A.controls x = false) (hh : human x = true)
    (s : State Agent Board Var Val Msg) :
    view (cfg.trusting A human) x s = emptyState := by
  simp [view, Config.trusting, hc, hh, emptyState]

/-- Two behaviours that choose alike give the same views. -/
theorem viewsOf_congr_choose (c : Config Agent Board Var Val Msg)
    {π₁ π₂ : Behaviour Agent Board Var Val Msg} {adv : Attack Agent Board Var Val Msg}
    (h : ∀ n x s, choose c A π₁ adv n x s = choose c A π₂ adv n x s) (a : Agent) :
    ∀ (sched : List (Turn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      viewsOf c A π₁ adv a sched s n = viewsOf c A π₂ adv a sched s n
  | [], _, _ => rfl
  | t :: ts, s, n => by
    have hs : step c A π₁ adv n t s = step c A π₂ adv n t s := by
      cases t with
      | agent x => simp only [step, h]
      | sys => rfl
    simp only [viewsOf, hs]
    rw [viewsOf_congr_choose c h a ts]

/-- The trusting version of a behaviour. Humans act as they would on an empty view, everyone else
as they would on their trusting view. -/
def Behaviour.trusted (π : Behaviour Agent Board Var Val Msg) : Behaviour Agent Board Var Val Msg :=
  fun x n s => if human x then π x n emptyState else π x n (view (cfg.trusting A human) x s)

theorem trusted_trusting (π : Behaviour Agent Board Var Val Msg) :
    Trusting human (Behaviour.trusted cfg A human π) := by
  intro h hh n s₁ s₂
  simp [Behaviour.trusted, hh]

/-- On the trusting configuration, the trusting version of a behaviour chooses as the behaviour does. -/
theorem choose_trusted (π : Behaviour Agent Board Var Val Msg)
    (adv : Attack Agent Board Var Val Msg) (n : Nat) (x : Agent)
    (s : State Agent Board Var Val Msg) :
    choose (cfg.trusting A human) A (Behaviour.trusted cfg A human π) adv n x s =
      choose (cfg.trusting A human) A π adv n x s := by
  unfold choose
  cases hc : A.controls x
  · simp only [Bool.false_eq_true, ite_false, Behaviour.trusted]
    cases hh : human x
    · simp only [Bool.false_eq_true, ite_false, view_idem]
    · simp only [ite_true, view_trusting_human cfg A human hc hh]
  · rfl

end exact

/-- Exactness with trusted humans. Under the hypotheses of `reach_iff_influence` for the
trusting configuration, an honest agent that is not a human is tainted exactly when some
behaviour whose honest humans ignore what they read, and some pair of attacker attacks, give it
different views. -/
theorem reach_trusting_iff_influence (W : Completeness.Setup Agent Board Var Val Msg)
    (human : Agent → Bool)
    (hA : ∀ a, a ∈ W.agents) (hB : ∀ b, b ∈ W.boards) (hV : ∀ v, v ∈ W.vars)
    (hecho : ∀ v, W.cfg.echoSees v = true → ∀ y, (W.cfg.trusting W.A human).sees y v = true)
    {a : Agent} (hc : W.A.controls a = false) (hh : human a = false) :
    Reach (W.cfg.trusting W.A human) W.A a ↔
      ∃ (honest : Behaviour Agent Board Var Val Msg), Trusting human honest ∧
        ∃ (adv₁ adv₂ : Attack Agent Board Var Val Msg)
          (sched : List (Turn Agent)) (s₀ : State Agent Board Var Val Msg),
          viewsOf W.cfg W.A honest adv₁ a sched s₀ ≠ viewsOf W.cfg W.A honest adv₂ a sched s₀ := by
  let W' : Completeness.Setup Agent Board Var Val Msg := { W with cfg := W.cfg.trusting W.A human }
  have key := Completeness.reach_iff_influence W' hA hB hV hecho hc
  have ha : W.A.controls a = true ∨ human a = false := Or.inr hh
  constructor
  · intro hr
    obtain ⟨π, adv₁, adv₂, sched, s₀, hne⟩ := key.mp hr
    let π' := Behaviour.trusted W.cfg W.A human π
    have ht : Trusting human π' := trusted_trusting W.cfg W.A human π
    refine ⟨π', ht, adv₁, adv₂, sched, s₀, ?_⟩
    intro heq
    apply hne
    have e : ∀ adv : Attack Agent Board Var Val Msg,
        viewsOf W.cfg W.A π' adv a sched s₀ =
          viewsOf (W.cfg.trusting W.A human) W.A π adv a sched s₀ := fun adv =>
      (viewsOf_trusting (cfg := W.cfg) (A := W.A) (adv := adv) ht ha sched s₀ 0).symm.trans
        (viewsOf_congr_choose W.A (W.cfg.trusting W.A human)
          (choose_trusted W.cfg W.A human π adv) a sched s₀ 0)
    rw [← e adv₁, ← e adv₂]
    exact heq
  · rintro ⟨π, ht, adv₁, adv₂, sched, s₀, hne⟩
    apply key.mpr
    refine ⟨π, adv₁, adv₂, sched, s₀, ?_⟩
    intro heq
    apply hne
    rw [← viewsOf_trusting (cfg := W.cfg) (A := W.A) (adv := adv₁) ht ha sched s₀ 0,
      ← viewsOf_trusting (cfg := W.cfg) (A := W.A) (adv := adv₂) ht ha sched s₀ 0]
    exact heq

end Ir
