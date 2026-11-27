import Ir.OrderedReach

/-!
# Every schedule at once

`reachSum_sound` holds for one fixed schedule. A taint state that every turn keeps inside
itself bounds the taint of every schedule, so an agent it leaves untainted is noninterferent
under any order of turns. For a summary that ignores the turn index (`Summary.uniform`), the
closure condition is a finite check, `closedB`, that `decide` can run.

- `taintAfter_le_closed`. A taint state closed under every turn, above the initial one, bounds
  `taintAfter` on every schedule.
- `closedB_sound`. The decidable check implies that bound for a uniform summary.
- `every_schedule_sound` and `every_schedule_board_sound`. Noninterference of each untainted
  agent and the final log of each untainted board, for every schedule and every behaviour that
  respects the summary.
- `Respects.of_kills`. A summary with the same dependencies and fewer kills is respected by
  every behaviour that respects the original. Generated modules assume a summary with kills on
  one schedule, and get the uniform summary without kills from it.
-/

set_option linter.unusedSectionVars false

namespace Ir

section

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]

/-- A summary that ignores the turn index. -/
def Summary.uniform (d : Agent → Loc Board Var → Loc Board Var → Bool)
    (k : Agent → Board → Bool) : Summary Agent Board Var :=
  ⟨fun x _ => d x, fun x _ => k x⟩

theorem Summary.finer_refl (S : Summary Agent Board Var) : S.Finer S :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ h => h⟩

/-- The same dependencies and fewer kills keep a summary respected. -/
theorem Respects.of_kills {S S' : Summary Agent Board Var}
    {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest) (hd : S'.dep = S.dep)
    (hk : ∀ x n b, S'.kills x n b = true → S.kills x n b = true) : Respects S' honest where
  dep x n o s₁ s₂ h := hR.dep x n o s₁ s₂ fun i hi => h i (by rw [hd]; exact hi)
  kills x n b s h := hR.kills x n b s (hk x n b h)

/-- `T` taints no more than `T'`, checked over the universe's lists. -/
def Taint.leB (U : Universe Agent Board Var) (T T' : Taint Agent Board Var) : Bool :=
  U.boards.all (fun b => !T.board b || T'.board b) &&
    U.vars.all (fun v => !T.var v || T'.var v) &&
      U.agents.all fun a => !T.agent a || T'.agent a

theorem Taint.le_of_leB {U : Universe Agent Board Var} {T T' : Taint Agent Board Var}
    (h : Taint.leB U T T' = true) : T.Le T' := by
  simp only [Taint.leB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hb, hv⟩, ha⟩ := h
  refine ⟨fun b hb' => ?_, fun v hv' => ?_, fun a ha' => ?_⟩
  · rcases hb b (U.hB b) with h | h
    · simp [h] at hb'
    · exact h
  · rcases hv v (U.hV v) with h | h
    · simp [h] at hv'
    · exact h
  · rcases ha a (U.hA a) with h | h
    · simp [h] at ha'
    · exact h

variable (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (U : Universe Agent Board Var) (S : Summary Agent Board Var)

/-- A taint state that every turn keeps inside itself bounds every schedule from below it. -/
theorem taintAfter_le_closed {T : Taint Agent Board Var}
    (hT : ∀ n t, (turnT cfg A U S n t T).Le T) :
    ∀ (ts : List (Turn Agent)) {T' : Taint Agent Board Var} (n : Nat), T'.Le T →
      (taintAfter cfg A U S ts T' n).Le T
  | [], _, _, h => h
  | t :: ts, _, n, h =>
    taintAfter_le_closed hT ts (n + 1)
      ((turnT_finer (Summary.finer_refl S) n t h).trans (hT n t))

/-- The closure condition for a uniform summary, as a finite check. -/
def closedB (d : Agent → Loc Board Var → Loc Board Var → Bool) (k : Agent → Board → Bool)
    (T : Taint Agent Board Var) : Bool :=
  Taint.leB U (Taint.init A) T && Taint.leB U (sysT A T) T &&
    U.agents.all fun x => Taint.leB U (agentT cfg A U (Summary.uniform d k) x 0 T) T

variable {cfg A U}

theorem closedB_sound {d : Agent → Loc Board Var → Loc Board Var → Bool}
    {k : Agent → Board → Bool} {T : Taint Agent Board Var} (h : closedB cfg A U d k T = true)
    (sched : List (Turn Agent)) :
    (taintAfter cfg A U (Summary.uniform d k) sched (Taint.init A) 0).Le T := by
  simp only [closedB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hi, hs⟩, ha⟩ := h
  refine taintAfter_le_closed cfg A U _ (fun n t => ?_) sched 0 (Taint.le_of_leB hi)
  cases t with
  | agent x => exact Taint.le_of_leB (ha x (U.hA x))
  | sys => exact Taint.le_of_leB hs

theorem reachSum_of_closedB {d : Agent → Loc Board Var → Loc Board Var → Bool}
    {k : Agent → Board → Bool} {T : Taint Agent Board Var} (h : closedB cfg A U d k T = true)
    (sched : List (Turn Agent)) {a : Agent} (ha : T.agent a = false) :
    reachSum cfg A U (Summary.uniform d k) sched a = false :=
  Bool.of_ne_true fun ht => by simp [(closedB_sound h sched).2.2 a ht] at ha

theorem boardSum_of_closedB {d : Agent → Loc Board Var → Loc Board Var → Bool}
    {k : Agent → Board → Bool} {T : Taint Agent Board Var} (h : closedB cfg A U d k T = true)
    (sched : List (Turn Agent)) {b : Board} (hb : T.board b = false) :
    boardSum cfg A U (Summary.uniform d k) sched b = false :=
  Bool.of_ne_true fun ht => by simp [(closedB_sound h sched).1 b ht] at hb

/-- Noninterference on every schedule. An agent the closed taint leaves untainted writes the
same actions to every output under any two attacker attacks, whatever the order of turns,
for every behaviour that respects the summary. -/
theorem every_schedule_sound {d : Agent → Loc Board Var → Loc Board Var → Bool}
    {k : Agent → Board → Bool} {T : Taint Agent Board Var} (h : closedB cfg A U d k T = true)
    {honest : Behaviour Agent Board Var Val Msg} (hR : Respects (Summary.uniform d k) honest)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) {a : Agent} (ha : T.agent a = false) (o : Loc Board Var) :
    (actionsOf cfg A honest adv₁ a sched s₀).map (List.filter (Action.touches o)) =
      (actionsOf cfg A honest adv₂ a sched s₀).map (List.filter (Action.touches o)) :=
  reachSum_sound hR adv₁ adv₂ s₀ sched a (reachSum_of_closedB h sched ha) o

/-- A board the closed taint leaves untainted ends with the same log on every schedule. -/
theorem every_schedule_board_sound {d : Agent → Loc Board Var → Loc Board Var → Bool}
    {k : Agent → Board → Bool} {T : Taint Agent Board Var} (h : closedB cfg A U d k T = true)
    {honest : Behaviour Agent Board Var Val Msg} (hR : Respects (Summary.uniform d k) honest)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) {b : Board} (hb : T.board b = false) :
    (run cfg A honest adv₁ sched s₀).logs b = (run cfg A honest adv₂ sched s₀).logs b :=
  boardSum_sound hR adv₁ adv₂ s₀ sched b (boardSum_of_closedB h sched hb)

end

end Ir
