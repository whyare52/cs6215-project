import Ir.ClearGap
import Ir.OrderedReach

/-!
# The clear closes the gap under an ordered analysis

`ClearGap.lean` shows `Reach` cannot tell kaymen99's bug from its fix. Here the same two
configs run the app's schedule. Customer A's email arrives and A's writer drafts, then the
reset node runs, then customer B's email arrives and B's writer drafts.

The reset node is plain code. Its summary is exact. Its outputs depend on nothing, and it
surely replaces `writerMessages`. Both writers stay black boxes. In the bug, the reset node
clears a throwaway copy, so it holds no write permission on the drafts and its replace does
nothing. In the fix it writes the drafts.

- `bug_taints_writeB` and `fix_clears_writeB`. The ordered analysis taints B's writer in
  the bug and not in the fix.
- `fix_writeB_noninterference`. So in the fix, B's writer writes the same actions to every
  output under any two attacks of customer A, for every behaviour whose reset node clears.
- `fix_taints_writeA`, `fix_drafts_tainted_before_clear`, `fix_blackBox_taints_writeB` and
  `fix_early_clear_taints_writeB`. A's flow still goes through the drafts, the clear helps
  only because its summary is exact, and only when it runs between the customers.
- `bug_leaks` and `fix_writeA_varies`. A concrete behaviour under which A's email changes B's
  writer in the bug, and A's own writer in the fix.
- `fix_safe_sessions`. For every order of customer sessions the runtime may choose, with the
  reset node after each session, the fix keeps B's writer untainted.
-/

namespace Ir.ClearGapClosed

open Ir.ClearGap ClearGap.Agent ClearGap.Board

/-- The reset node is code that depends on nothing and surely clears the drafts. Both writers
are black boxes. -/
def resetCode : Summary Agent Board Empty where
  dep x _ _ _ := !decide (x = reset)
  kills x _ b := decide (x = reset) && decide (b = writerMessages)

/-- One customer's session, followed by the reset node. -/
def sessions (ss : List (Agent × List (Turn Agent))) : List (Turn Agent) :=
  (ss.map fun p => p.2 ++ [.agent reset]).flatten

/-- The app's schedule. A's email and writer, the reset, then B's email and writer. -/
def app : List (Turn Agent) :=
  sessions [(writeA, [.sys, .agent writeA]), (writeB, [.sys, .agent writeB])]

example : app = [.sys, .agent writeA, .agent reset, .sys, .agent writeB, .agent reset] := rfl

/-! ## The verdicts -/

theorem bug_taints_writeB : reachSum bug customerA world resetCode app writeB = true := by
  decide

theorem fix_clears_writeB : reachSum fix customerA world resetCode app writeB = false := by
  decide

/-- The drafts end clean in the fix and tainted in the bug. -/
example : boardSum fix customerA world resetCode app writerMessages = false := by decide
example : boardSum bug customerA world resetCode app writerMessages = true := by decide

/-- A behaviour respects the summary when its reset node clears the drafts. -/
theorem respects_resetCode (honest : Behaviour Agent Board Empty Nat String)
    (h : ∀ n s, honest reset n s = [.clear writerMessages]) : Respects resetCode honest where
  dep x n o s₁ s₂ hag := by
    by_cases hx : x = reset
    · subst hx; rw [h, h]
    · exact (respects_blackBox honest).dep x n o s₁ s₂ fun i _ =>
        hag i (by simp [resetCode, hx])
  kills x n b s hk := by
    simp only [resetCode, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨none, by simp [h]⟩

theorem fix_writeB_noninterference (honest : Behaviour Agent Board Empty Nat String)
    (hR : Respects resetCode honest) (adv₁ adv₂ : Attack Agent Board Empty Nat String)
    (s₀ : State Agent Board Empty Nat String) (o : Loc Board Empty) :
    (actionsOf fix customerA honest adv₁ writeB app s₀).map (List.filter (Action.touches o)) =
      (actionsOf fix customerA honest adv₂ writeB app s₀).map
        (List.filter (Action.touches o)) :=
  reachSum_sound hR adv₁ adv₂ s₀ app writeB fix_clears_writeB o

/-! ## The clear is not vacuous -/

theorem fix_taints_writeA : reachSum fix customerA world resetCode app writeA = true := by
  decide

/-- Before the clear, A's drafts carry A's influence. -/
theorem fix_drafts_tainted_before_clear :
    boardSum fix customerA world resetCode [.sys, .agent writeA] writerMessages = true := by
  decide

/-- With a black-box reset node the fix still taints B's writer. -/
theorem fix_blackBox_taints_writeB :
    reachSum fix customerA world Summary.blackBox app writeB = true := by
  decide

/-- A clear before A's session does not help. -/
theorem fix_early_clear_taints_writeB :
    reachSum fix customerA world resetCode
      [.agent reset, .sys, .agent writeA, .sys, .agent writeB] writeB = true := by
  decide

/-! ## A concrete leak -/

/-- Each writer copies what it reads into the drafts, and the reset node clears them. -/
def copyBehaviour : Behaviour Agent Board Empty Nat String
  | writeA, _, s => (s.logs emailA).map fun e => .post writerMessages e.2
  | writeB, _, s => (s.logs writerMessages).map fun e => .post writerMessages e.2
  | reset, _, _ => [.clear writerMessages]

theorem copyBehaviour_respects : Respects resetCode copyBehaviour :=
  respects_resetCode copyBehaviour fun _ _ => rfl

/-- Customer A sends the email `m`. -/
def sends (m : String) : Attack Agent Board Empty Nat String where
  act _ _ _ := []
  inject _ _ := some (emailA, m)

def empty : State Agent Board Empty Nat String where
  logs _ := []
  assign v := nomatch v

theorem bug_writeB_sees (m : String) :
    actionsOf bug customerA copyBehaviour (sends m) writeB app empty =
      [[.post writerMessages m]] := rfl

theorem fix_writeB_sees (m : String) :
    actionsOf fix customerA copyBehaviour (sends m) writeB app empty = [[]] := rfl

theorem fix_writeA_sees (m : String) :
    actionsOf fix customerA copyBehaviour (sends m) writeA app empty =
      [[.post writerMessages m]] := rfl

/-- In the bug, A's email changes what B's writer does. -/
theorem bug_leaks :
    actionsOf bug customerA copyBehaviour (sends "x") writeB app empty ≠
      actionsOf bug customerA copyBehaviour (sends "y") writeB app empty := by
  rw [bug_writeB_sees, bug_writeB_sees]
  simp

/-- In the fix, A's email still changes what A's own writer does. -/
theorem fix_writeA_varies :
    actionsOf fix customerA copyBehaviour (sends "x") writeA app empty ≠
      actionsOf fix customerA copyBehaviour (sends "y") writeA app empty := by
  rw [fix_writeA_sees, fix_writeA_sees]
  simp

/-! ## Every session order -/

/-- A session holds one customer's turns. Their email arriving and their writer drafting, in
any order and number. -/
def OneCustomer (p : Agent × List (Turn Agent)) : Prop :=
  (p.1 = writeA ∨ p.1 = writeB) ∧ ∀ t ∈ p.2, t = .sys ∨ t = .agent p.1

/-- Outside A's sessions B's writer is clean, and so are B's email and the drafts. -/
def Clean (T : Taint Agent Board Empty) : Prop :=
  T.agent writeB = false ∧ T.board writerMessages = false ∧ T.board emailB = false

/-- During A's session only the drafts may be dirty. -/
def CleanA (T : Taint Agent Board Empty) : Prop :=
  T.agent writeB = false ∧ T.board emailB = false

theorem cleanA_turn (n : Nat) (t : Turn Agent) (ht : t = .sys ∨ t = .agent writeA)
    {T : Taint Agent Board Empty} (h : CleanA T) :
    CleanA (turnT fix customerA world resetCode n t T) := by
  obtain ⟨h₁, h₂⟩ := h
  rcases ht with rfl | rfl
  · exact ⟨h₁, by simp [turnT, sysT, customerA, h₂]⟩
  · refine ⟨?_, ?_⟩
    · simp [turnT, agentT, h₁]
    · simp [turnT, agentT, fix, bug, h₂]

theorem clean_turn (n : Nat) (t : Turn Agent) (ht : t = .sys ∨ t = .agent writeB)
    {T : Taint Agent Board Empty} (h : Clean T) :
    Clean (turnT fix customerA world resetCode n t T) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  rcases ht with rfl | rfl
  · exact ⟨h₁, by simp [turnT, sysT, customerA, h₂], by simp [turnT, sysT, customerA, h₃]⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [turnT, agentT, h₁, customerA, inT, Universe.locs, world, readT, fix, bug,
        resetCode, h₂, h₃]
    · simp [turnT, agentT, customerA, hot, inT, Universe.locs, world, readT, fix, bug,
        resetCode, h₂, h₃, ownsVar]
    · simp [turnT, agentT, fix, bug, h₃]

theorem clean_reset (n : Nat) {T : Taint Agent Board Empty} (h : CleanA T) :
    Clean (turnT fix customerA world resetCode n (.agent reset) T) := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp [turnT, agentT, h₁]
  · simp [turnT, agentT, customerA, hot, inT, Universe.locs, world, readT, fix, bug,
      resetCode, ownsVar]
  · simp [turnT, agentT, fix, bug, h₂]

theorem session_cleanA (c : Agent) (hc : c = writeA) :
    ∀ (ts : List (Turn Agent)) (T : Taint Agent Board Empty) (n : Nat),
      (∀ t ∈ ts, t = .sys ∨ t = .agent c) → CleanA T →
      CleanA (taintAfter fix customerA world resetCode ts T n)
  | [], _, _, _, h => h
  | t :: ts, _, n, hts, h =>
    session_cleanA c hc ts _ _ (fun t' hm => hts t' (List.mem_cons_of_mem _ hm))
      (cleanA_turn n t (hc ▸ hts t List.mem_cons_self) h)

theorem session_clean (c : Agent) (hc : c = writeB) :
    ∀ (ts : List (Turn Agent)) (T : Taint Agent Board Empty) (n : Nat),
      (∀ t ∈ ts, t = .sys ∨ t = .agent c) → Clean T →
      Clean (taintAfter fix customerA world resetCode ts T n)
  | [], _, _, _, h => h
  | t :: ts, _, n, hts, h =>
    session_clean c hc ts _ _ (fun t' hm => hts t' (List.mem_cons_of_mem _ hm))
      (clean_turn n t (hc ▸ hts t List.mem_cons_self) h)

/-- Schedule-free. Whatever order of sessions the runtime picks, as long as the reset node runs
after each, B's writer stays untainted in the fix. -/
theorem fix_safe_sessions (ss : List (Agent × List (Turn Agent)))
    (hss : ∀ p ∈ ss, OneCustomer p) :
    reachSum fix customerA world resetCode (sessions ss) writeB = false := by
  have hblk := taintAfter_blocks fix customerA world resetCode Clean
    (fun blk => ∃ p, OneCustomer p ∧ blk = p.2 ++ [.agent reset])
    (by
      rintro blk ⟨⟨c, ts⟩, ⟨hc, hts⟩, rfl⟩ T n hT
      rw [taintAfter_append]
      simp only [taintAfter]
      rcases hc with rfl | rfl
      · exact clean_reset _ (session_cleanA writeA rfl ts T n hts ⟨hT.1, hT.2.2⟩)
      · have h := session_clean writeB rfl ts T n hts hT
        exact clean_reset _ ⟨h.1, h.2.2⟩)
    (ss.map fun p => p.2 ++ [.agent reset])
    (by
      intro blk hm
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      exact ⟨p, hss p hp, rfl⟩)
    (Taint.init customerA) 0 ⟨rfl, rfl, rfl⟩
  exact hblk.1

/-- The app's schedule is one such order, so the bug's verdict is not an artefact of it. -/
example : ∀ p ∈ [(writeA, [Turn.sys, .agent writeA]), (writeB, [.sys, .agent writeB])],
    OneCustomer p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> refine ⟨by simp, ?_⟩ <;> intro t ht <;> simp at ht <;> simp [ht]

end Ir.ClearGapClosed
