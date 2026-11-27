import Ir.ContractNoninterference
import Ir.Check

/-!
# Parallel supersteps

LangGraph runs the nodes of one superstep in parallel. Each reads the state as it was when
the superstep began, and their writes are applied afterwards, in order. The protocol runs one
turn at a time, each reading the state the previous turns left.

The two agree when no agent in a superstep can see what an earlier one in it writes
(`Blind`). Then every superstep run is a guarded protocol run under the same honest behaviour.
The attacker's attack changes, since it reads the full state, but noninterference already
holds for every attack, so it carries over (`assign_fixed_par`).
-/

set_option linter.unusedSectionVars false

namespace Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]

/-- Agent `x` cannot see what `y` writes. `x` reads no board `y` writes, and sees no variable
`y` owns. Echoes of `y`'s commits go to the boards `y` writes, so they are covered too. -/
def Blind (cfg : Config Agent Board Var Val Msg) (x y : Agent) : Prop :=
  (∀ b, cfg.writer b y = true → cfg.reader b x = false) ∧
    ∀ v, cfg.owner v = y → cfg.sees x v = false

theorem view_perform_blind {cfg : Config Agent Board Var Val Msg} {x y : Agent}
    (hxy : Blind cfg x y) (act : Action Board Var Val Msg)
    (s : State Agent Board Var Val Msg) :
    view cfg x (perform cfg y act s) = view cfg x s := by
  cases act with
  | post b m =>
    simp only [perform]
    split
    · rename_i hy
      simp only [view, post, State.mk.injEq]
      refine ⟨funext fun b' => ?_, trivial⟩
      by_cases hb : b' = b
      · subst hb; simp [hxy.1 _ hy]
      · simp [hb]
    · rfl
  | replace b m =>
    simp only [perform]
    split
    · rename_i hy
      simp only [view, setLog, State.mk.injEq]
      refine ⟨funext fun b' => ?_, trivial⟩
      by_cases hb : b' = b
      · subst hb; simp [hxy.1 _ hy]
      · simp [hb]
    · rfl
  | attend v t =>
    simp only [perform]
    split
    · rename_i hown
      simp only [view, commit, State.mk.injEq]
      refine ⟨funext fun b => ?_, funext fun v' => ?_⟩
      · cases hx : cfg.reader b x with
        | false => rfl
        | true =>
          cases hy : cfg.writer b y with
          | false => rfl
          | true => simp [hxy.1 b hy] at hx
      · by_cases hv : v' = v
        · subst hv; simp [hxy.2 _ hown.1]
        · simp [hv]
    · rfl
  | skip => rfl

theorem view_performC_blind {cfg : Config Agent Board Var Val Msg}
    (C : Contract Agent Board Var Val Msg) {x y : Agent} (hxy : Blind cfg x y) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      view cfg x (performC cfg C y acts s) = view cfg x s
  | [], _ => rfl
  | act :: acts, s => by
    simp only [performC]
    rw [view_performC_blind C hxy acts, view_perform_blind hxy]

section

variable (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (honest : Behaviour Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg)

/-- The agents of one superstep, each choosing from the snapshot `s₀` and guarded against
the state the earlier writes left. Turn indices count up from `n`. -/
def applyFrom (adv : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg) :
    List Agent → State Agent Board Var Val Msg → Nat → State Agent Board Var Val Msg
  | [], s, _ => s
  | x :: xs, s, n =>
    applyFrom adv s₀ xs (performC cfg C x (choose cfg A honest adv n x s₀) s) (n + 1)

/-- A turn of the parallel schedule. A superstep of agents, or one SYS turn. -/
inductive PTurn (Agent : Type) where
  | par (xs : List Agent)
  | sys

/-- The turns a parallel turn takes in the sequential schedule. -/
def PTurn.flat : PTurn Agent → List (Turn Agent)
  | .par xs => xs.map .agent
  | .sys => [.sys]

def PTurn.width : PTurn Agent → Nat
  | .par xs => xs.length
  | .sys => 1

/-- A parallel run. Each superstep reads its starting state. -/
def runPar (adv : Attack Agent Board Var Val Msg) :
    List (PTurn Agent) → State Agent Board Var Val Msg → optParam Nat 0 →
    State Agent Board Var Val Msg
  | [], s, _ => s
  | .par xs :: ps, s, n => runPar adv ps (applyFrom cfg A honest C adv s xs s n) (n + xs.length)
  | .sys :: ps, s, n => runPar adv ps (sysStep A adv n s) (n + 1)

/-- Every agent in a superstep is blind to the agents before it. -/
def PTurn.Ok : PTurn Agent → Prop
  | .par xs => xs.Pairwise (fun y x => Blind cfg x y)
  | .sys => True

end

/-- A guarded run depends on the attack only from its starting index on. -/
theorem runC_congr {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {honest : Behaviour Agent Board Var Val Msg} {C : Contract Agent Board Var Val Msg}
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} :
    ∀ (sched : List (Turn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      (∀ x m s, n ≤ m → adv₁.act x m s = adv₂.act x m s) →
      (∀ m s, n ≤ m → adv₁.inject m s = adv₂.inject m s) →
      runC cfg A honest adv₁ C sched s n = runC cfg A honest adv₂ C sched s n
  | [], _, _, _, _ => rfl
  | t :: ts, s, n, ha, hi => by
    simp only [runC]
    have hstep : stepC cfg A honest adv₁ C n t s = stepC cfg A honest adv₂ C n t s := by
      cases t with
      | agent x => simp only [stepC, choose, ha x n s (Nat.le_refl n)]
      | sys => simp only [stepC, sysStep, hi n s (Nat.le_refl n)]
    rw [hstep]
    exact runC_congr ts _ (n + 1) (fun x m s h => ha x m s (by omega))
      (fun m s h => hi m s (by omega))

theorem runC_append {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {honest : Behaviour Agent Board Var Val Msg} {C : Contract Agent Board Var Val Msg}
    {adv : Attack Agent Board Var Val Msg} :
    ∀ (t₁ t₂ : List (Turn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      runC cfg A honest adv C (t₁ ++ t₂) s n =
        runC cfg A honest adv C t₂ (runC cfg A honest adv C t₁ s n) (n + t₁.length)
  | [], _, _, _ => rfl
  | t :: ts, t₂, s, n => by
    simp only [List.cons_append, runC, List.length_cons]
    rw [runC_append ts, show n + 1 + ts.length = n + (ts.length + 1) by omega]

/-- One superstep is a sequential run, if every agent is blind to the earlier ones, no agent
has seen a change since the snapshot, and the new attack acts as the old one did on the
snapshot. -/
theorem applyFrom_eq {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {honest : Behaviour Agent Board Var Val Msg} {C : Contract Agent Board Var Val Msg}
    (adv adv' : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg) :
    ∀ (xs : List Agent) (s : State Agent Board Var Val Msg) (n : Nat),
      xs.Pairwise (fun y x => Blind cfg x y) →
      (∀ x ∈ xs, view cfg x s = view cfg x s₀) →
      (∀ x m s, n ≤ m → m < n + xs.length → adv'.act x m s = adv.act x m s₀) →
      applyFrom cfg A honest C adv s₀ xs s n =
        runC cfg A honest adv' C (xs.map .agent) s n
  | [], _, _, _, _, _ => rfl
  | x :: xs, s, n, hp, hv, ha => by
    cases hp with
    | cons hx hp =>
      simp only [applyFrom, List.map, runC, stepC]
      have hc : choose cfg A honest adv n x s₀ = choose cfg A honest adv' n x s := by
        simp only [choose]
        cases hcx : A.controls x with
        | true =>
          simp only [↓reduceIte]
          exact (ha x n s (Nat.le_refl n) (by simp only [List.length_cons]; omega)).symm
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hv x (by simp)]
      rw [hc]
      apply applyFrom_eq adv adv' s₀ xs _ (n + 1) hp
      · intro y hy
        rw [view_performC_blind C (hx y hy), hv y (by simp [hy])]
      · intro y m s h1 h2
        exact ha y m s (by omega) (by simp only [List.length_cons]; omega)

/-- Every parallel run whose supersteps are `Ok` is a guarded sequential run under the same
honest behaviour, for some attacker attack with the same injections. -/
theorem runPar_eq {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    {honest : Behaviour Agent Board Var Val Msg} {C : Contract Agent Board Var Val Msg}
    (adv : Attack Agent Board Var Val Msg) :
    ∀ (ps : List (PTurn Agent)) (s : State Agent Board Var Val Msg) (n : Nat),
      (∀ p ∈ ps, PTurn.Ok cfg p) →
      ∃ adv' : Attack Agent Board Var Val Msg,
        (∀ m s, adv'.inject m s = adv.inject m s) ∧
        runPar cfg A honest C adv ps s n =
          runC cfg A honest adv' C (ps.flatMap PTurn.flat) s n
  | [], _, _, _ => ⟨adv, fun _ _ => rfl, rfl⟩
  | .sys :: ps, s, n, hok => by
    obtain ⟨adv'', hi, he⟩ := runPar_eq adv ps (sysStep A adv n s) (n + 1)
      (fun p hp => hok p (by simp [hp]))
    refine ⟨adv'', hi, ?_⟩
    simp only [runPar, List.flatMap_cons, PTurn.flat, List.singleton_append, runC, stepC]
    have hs : sysStep A adv'' n s = sysStep A adv n s := by simp only [sysStep, hi]
    rw [hs, he]
  | .par xs :: ps, s, n, hok => by
    obtain ⟨adv'', hi, he⟩ := runPar_eq adv ps (applyFrom cfg A honest C adv s xs s n)
      (n + xs.length) (fun p hp => hok p (by simp [hp]))
    let adv' : Attack Agent Board Var Val Msg :=
      { act := fun x m s' => if m < n + xs.length then adv.act x m s else adv''.act x m s'
        inject := adv''.inject }
    refine ⟨adv', hi, ?_⟩
    have hseq := applyFrom_eq (cfg := cfg) (A := A) (honest := honest) (C := C) adv adv' s
      xs s n (hok (.par xs) (by simp)) (fun _ _ => rfl)
      (fun x m s' _ h => by simp only [adv', h, ↓reduceIte])
    rw [List.flatMap_cons, runC_append]
    simp only [PTurn.flat, List.length_map]
    rw [← hseq]
    simp only [runPar]
    rw [he]
    apply runC_congr
    · intro x m s' h
      have hm : ¬ m < n + xs.length := by omega
      simp only [adv', hm, ↓reduceIte]
    · intro m s' _
      rfl

/-- `Blind` decided over a finite universe. -/
def blindB (cfg : Config Agent Board Var Val Msg) (U : Universe Agent Board Var)
    (x y : Agent) : Bool :=
  U.boards.all (fun b => !(cfg.writer b y && cfg.reader b x)) &&
    U.vars.all (fun v => !(decide (cfg.owner v = y) && cfg.sees x v))

theorem blindB_sound {cfg : Config Agent Board Var Val Msg} {U : Universe Agent Board Var}
    {x y : Agent} (h : blindB cfg U x y = true) : Blind cfg x y := by
  simp only [blindB, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun b hy => ?_, fun v hv => ?_⟩
  · have := h.1 b (U.hB b); simp_all
  · have := h.2 v (U.hV v); simp_all

/-- `PTurn.Ok` decided over a finite universe. -/
def okB (cfg : Config Agent Board Var Val Msg) (U : Universe Agent Board Var) :
    PTurn Agent → Bool
  | .par xs => go xs
  | .sys => true
where
  go : List Agent → Bool
    | [] => true
    | y :: xs => xs.all (fun x => blindB cfg U x y) && go xs

theorem okB_sound {cfg : Config Agent Board Var Val Msg} {U : Universe Agent Board Var} :
    ∀ {p : PTurn Agent}, okB cfg U p = true → PTurn.Ok cfg p
  | .sys, _ => trivial
  | .par xs, h => go xs h
where
  go : ∀ (xs : List Agent), okB.go cfg U xs = true →
      xs.Pairwise (fun y x => Blind cfg x y)
    | [], _ => .nil
    | y :: xs, h => by
      simp only [okB.go, Bool.and_eq_true, List.all_eq_true] at h
      exact .cons (fun x hx => blindB_sound (h.1 x hx)) (go xs h.2)

/-- Noninterference for parallel runs. A variable with an unreachable owner ends with the
same value under any two attacker attacks, if every superstep is `Ok`. -/
theorem assign_fixed_par (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
    (C : Contract Agent Board Var Val Msg) (hC : RespectsAgree cfg A C)
    (s₀ : State Agent Board Var Val Msg) (ps : List (PTurn Agent))
    (hok : ∀ p ∈ ps, PTurn.Ok cfg p) (v : Var) (hv : ¬ Reach cfg A (cfg.owner v)) :
    (runPar cfg A honest C adv₁ ps s₀).assign v =
      (runPar cfg A honest C adv₂ ps s₀).assign v := by
  obtain ⟨a₁, _, h₁⟩ := runPar_eq (cfg := cfg) (A := A) (honest := honest) (C := C)
    adv₁ ps s₀ 0 hok
  obtain ⟨a₂, _, h₂⟩ := runPar_eq (cfg := cfg) (A := A) (honest := honest) (C := C)
    adv₂ ps s₀ 0 hok
  rw [h₁, h₂]
  exact assign_fixedC cfg A honest a₁ a₂ C hC s₀ _ v hv

end Ir
