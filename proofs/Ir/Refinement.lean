import Ir.ContractNoninterference

/-!
# Refinement of a monitored host into the protocol

A host is a framework such as LangGraph running the protocol's agents as nodes under a
monitor. Its state is the framework's own, and `abs` reads the protocol state out of it.
The monitor does three things, each stated as a law below.

- `mask_view`. A node sees a masked host state, and the mask depends only on the agent's
  protocol view.
- `apply_abs`. The monitor applies a node's actions as `performC` would.
- `post_abs`. An outside injection lands as a SYS post.

Nodes are arbitrary functions of the turn index and the masked state, so they cover any LLM.
Under the laws every host run is a guarded protocol run (`refine`), so every theorem about
`runC` holds of the host. The laws are the trusted base. The Python monitor is meant to
satisfy them, and its tests check it against the Lean transitions.
-/

namespace Ir

/-- A host framework running the protocol under a monitor. -/
structure Host (Agent Board Var Val Msg : Type)
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg) where
  HState : Type
  inh : Nonempty HState
  abs : HState → State Agent Board Var Val Msg
  mask : Agent → HState → HState
  apply : Agent → List (Action Board Var Val Msg) → HState → HState
  postSys : Board → Msg → HState → HState
  mask_view : ∀ a h₁ h₂, view cfg a (abs h₁) = view cfg a (abs h₂) → mask a h₁ = mask a h₂
  apply_abs : ∀ a acts h, abs (apply a acts h) = performC cfg C a acts (abs h)
  post_abs : ∀ b m h, abs (postSys b m h) = post b (none, m) (abs h)

namespace Host

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg} {C : Contract Agent Board Var Val Msg}
  (H : Host Agent Board Var Val Msg cfg C) (A : Adversary Agent Board)

/-- A node chooses its turn's actions from the turn index and the state the monitor shows. -/
abbrev Node := Agent → Nat → H.HState → List (Action Board Var Val Msg)

/-- The attacker's outside writes, chosen from the protocol state. -/
abbrev Inject := Nat → State Agent Board Var Val Msg → Option (Board × Msg)

/-- One host step. Controlled agents run the attacker's nodes, the rest the honest ones. -/
def step (hn an : H.Node) (inj : Inject (Agent := Agent) (Board := Board) (Var := Var)
    (Val := Val) (Msg := Msg)) (n : Nat) : Turn Agent → H.HState → H.HState
  | .agent x, h =>
    H.apply x ((if A.controls x then an x n (H.mask x h) else hn x n (H.mask x h))) h
  | .sys, h =>
    match inj n (H.abs h) with
    | some (b, m) => if A.injects b then H.postSys b m h else h
    | none => h

/-- A host run over a schedule. The monitor fixes the schedule, as it owns the routing. -/
def run (hn an : H.Node) (inj : Inject (Agent := Agent) (Board := Board) (Var := Var)
    (Val := Val) (Msg := Msg)) :
    List (Turn Agent) → H.HState → optParam Nat 0 → H.HState
  | [], h, _ => h
  | t :: ts, h, n => run hn an inj ts (step H A hn an inj n t h) (n + 1)

/-- Some host state with the given view, if there is one. -/
noncomputable def pickView (a : Agent) (v : State Agent Board Var Val Msg) : H.HState :=
  @Classical.epsilon _ H.inh (fun h => view cfg a (H.abs h) = v)

/-- Some host state with the given protocol state, if there is one. -/
noncomputable def pickState (s : State Agent Board Var Val Msg) : H.HState :=
  @Classical.epsilon _ H.inh (fun h => H.abs h = s)

/-- The protocol behaviour of honest nodes. It runs the node on a host state with that view. -/
noncomputable def behaviour (hn : H.Node) : Behaviour Agent Board Var Val Msg :=
  fun a n v => hn a n (H.mask a (H.pickView a v))

/-- The protocol attack of the attacker's nodes and injections. -/
noncomputable def attack (an : H.Node) (inj : Inject (Agent := Agent) (Board := Board)
    (Var := Var) (Val := Val) (Msg := Msg)) : Attack Agent Board Var Val Msg where
  act a n s := an a n (H.mask a (H.pickState s))
  inject := inj

theorem mask_pickView (a : Agent) (h : H.HState) :
    H.mask a (H.pickView a (view cfg a (H.abs h))) = H.mask a h :=
  H.mask_view a _ h
    (Classical.epsilon_spec_aux H.inh (fun h' => view cfg a (H.abs h') = view cfg a (H.abs h))
      ⟨h, rfl⟩)

theorem mask_pickState (a : Agent) (h : H.HState) :
    H.mask a (H.pickState (H.abs h)) = H.mask a h :=
  H.mask_view a _ h (by
    have hs : H.abs (H.pickState (H.abs h)) = H.abs h :=
      Classical.epsilon_spec_aux H.inh (fun h' => H.abs h' = H.abs h) ⟨h, rfl⟩
    rw [hs])

/-- On a real host state, the protocol chooses what the host's node chooses. -/
theorem choose_eq_node (hn an : H.Node) (inj : Inject (Agent := Agent) (Board := Board)
    (Var := Var) (Val := Val) (Msg := Msg)) (n : Nat) (x : Agent) (h : H.HState) :
    choose cfg A (H.behaviour hn) (H.attack an inj) n x (H.abs h) =
      (if A.controls x then an x n (H.mask x h) else hn x n (H.mask x h)) := by
  simp only [choose, behaviour, attack]
  split
  · rw [mask_pickState]
  · rw [mask_pickView]

/-- One host step is one guarded protocol step. -/
theorem step_abs (hn an : H.Node) (inj : Inject (Agent := Agent) (Board := Board)
    (Var := Var) (Val := Val) (Msg := Msg)) (n : Nat) (t : Turn Agent) (h : H.HState) :
    H.abs (step H A hn an inj n t h) =
      stepC cfg A (H.behaviour hn) (H.attack an inj) C n t (H.abs h) := by
  cases t with
  | agent x =>
    simp only [step, stepC]
    rw [H.apply_abs, choose_eq_node]
  | sys =>
    simp only [step, stepC, sysStep, attack]
    cases inj n (H.abs h) with
    | none => rfl
    | some p =>
      obtain ⟨b, m⟩ := p
      simp only
      split
      · exact H.post_abs b m h
      · rfl

/-- Refinement. Every monitored host run is a guarded protocol run, under the behaviour of the
honest nodes and the attack of the attacker. -/
theorem refine (hn an : H.Node) (inj : Inject (Agent := Agent) (Board := Board)
    (Var := Var) (Val := Val) (Msg := Msg)) :
    ∀ (sched : List (Turn Agent)) (h : H.HState) (n : Nat),
      H.abs (run H A hn an inj sched h n) =
        runC cfg A (H.behaviour hn) (H.attack an inj) C sched (H.abs h) n
  | [], _, _ => rfl
  | t :: ts, h, n => by
    simp only [run, runC]
    rw [refine hn an inj ts _ (n + 1), step_abs]

/-- Noninterference on the host. Whatever the attacker's nodes and injections, a variable
whose owner is unreachable ends with the same value, for any honest nodes. -/
theorem assign_fixed (hC : RespectsAgree cfg A C) (hn an₁ an₂ : H.Node)
    (inj₁ inj₂ : Inject (Agent := Agent) (Board := Board) (Var := Var) (Val := Val)
      (Msg := Msg))
    (h₀ : H.HState) (sched : List (Turn Agent)) (v : Var)
    (hv : ¬ Reach cfg A (cfg.owner v)) :
    (H.abs (run H A hn an₁ inj₁ sched h₀)).assign v =
      (H.abs (run H A hn an₂ inj₂ sched h₀)).assign v := by
  rw [refine, refine]
  exact assign_fixedC cfg A (H.behaviour hn) _ _ C hC (H.abs h₀) sched v hv

/-- Contract invariants on the host. An invariant that allowed actions and SYS keep holds of
the protocol state along every monitored run, whatever any node does. -/
theorem invariant (I : State Agent Board Var Val Msg → Prop)
    (hact : ∀ x s act, I s → C x s act = true → I (perform cfg x act s))
    (hsys : ∀ (adv : Attack Agent Board Var Val Msg) n s, I s → I (sysStep A adv n s))
    (hn an : H.Node) (inj : Inject (Agent := Agent) (Board := Board) (Var := Var)
      (Val := Val) (Msg := Msg))
    (sched : List (Turn Agent)) (h₀ : H.HState) (h : I (H.abs h₀)) :
    I (H.abs (run H A hn an inj sched h₀)) := by
  rw [refine]
  exact runC_invariant cfg A _ _ C I hact (hsys _) sched _ 0 h

end Host

/-- The reference host. Its state is the protocol state, a node sees its view, and the
monitor performs the guarded turn. It shows the laws can hold. -/
def Host.reference {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg) :
    Host Agent Board Var Val Msg cfg C where
  HState := State Agent Board Var Val Msg
  inh := ⟨{ logs := fun _ => [], assign := fun _ => none }⟩
  abs := id
  mask a s := view cfg a s
  apply a acts s := performC cfg C a acts s
  postSys b m s := post b (none, m) s
  mask_view _ _ _ h := h
  apply_abs _ _ _ := rfl
  post_abs _ _ _ := rfl

end Ir
