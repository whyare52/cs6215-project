import Ir.Refinement

/-!
# Masks that factor through the view

`py/lgmonitor.py` in `block` mode hands a node, for each value it may not read, a value
computed from what its agent may read. This file shows that any such mask satisfies the
`mask_view` law, so `Host.refine` and `Host.assign_fixed` hold of it, and pins down which
substitute the monitor may choose.

- `Host.ofView`. A host whose mask is any function of the agent's view. `Host.reference` is
  the case where the function is the identity.
- `newest`. The monitor's substitute for a location, the newest entry among the writers the
  reader may read, each writer's part being its board `c#P<-w`. `newest_congr` says it reads
  only those boards, so it is a function of the view.
- `latest_not_of_parts`. Without stamps, the newest visible entry of a location is not a
  function of its per-writer parts, since two interleavings have the same parts. So the
  monitor stamps each write with a global sequence number and compares stamps.
-/

namespace Ir

/-- A host whose state is the protocol state and whose mask is `f` applied to the view. -/
def Host.ofView {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg)
    (f : Agent → State Agent Board Var Val Msg → State Agent Board Var Val Msg) :
    Host Agent Board Var Val Msg cfg C where
  HState := State Agent Board Var Val Msg
  inh := ⟨{ logs := fun _ => [], assign := fun _ => none }⟩
  abs := id
  mask a s := f a (view cfg a s)
  apply a acts s := performC cfg C a acts s
  postSys b m s := post b (none, m) s
  mask_view a _ _ h := congrArg (f a) h
  apply_abs _ _ _ := rfl
  post_abs _ _ _ := rfl

/-- The reference host masks with the view itself. -/
theorem Host.reference_ofView {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg) :
    Host.reference cfg C = Host.ofView cfg C (fun _ v => v) := rfl

/-- Noninterference for every view-factored mask, whatever it substitutes. -/
theorem Host.ofView_assign_fixed {Agent Board Var Val Msg : Type}
    [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
    (cfg : Config Agent Board Var Val Msg) (C : Contract Agent Board Var Val Msg)
    (A : Adversary Agent Board) (hC : RespectsAgree cfg A C)
    (f : Agent → State Agent Board Var Val Msg → State Agent Board Var Val Msg)
    (hn an₁ an₂ : (Host.ofView cfg C f).Node)
    (inj₁ inj₂ : Host.Inject (Agent := Agent) (Board := Board) (Var := Var) (Val := Val)
      (Msg := Msg))
    (h₀ : State Agent Board Var Val Msg) (sched : List (Turn Agent)) (v : Var)
    (hv : ¬ Reach cfg A (cfg.owner v)) :
    ((Host.ofView cfg C f).run A hn an₁ inj₁ sched h₀).assign v =
      ((Host.ofView cfg C f).run A hn an₂ inj₂ sched h₀).assign v :=
  Host.assign_fixed _ A hC hn an₁ an₂ inj₁ inj₂ h₀ sched v hv

section Location

variable {W M : Type} [DecidableEq W]

/-- What writer `w` put at a location, its board `c#P<-w` in the extracted spec. -/
def part (w : W) (l : List (W × M)) : List (W × M) :=
  l.filter (fun e => decide (e.1 = w))

/-- Of two candidates, the one with the larger stamp. -/
def pick (st : M → Nat) : Option M → Option M → Option M
  | none, y => y
  | x, none => x
  | some x, some y => if st x ≤ st y then some y else some x

/-- The monitor's substitute. Each writer `w` in `ws` that the reader may read (`ok w`)
offers the last entry of its part, and the largest stamp wins. -/
def newest (st : M → Nat) (ok : W → Bool) (ws : List W) (l : List (W × M)) : Option M :=
  ws.foldr (fun w acc =>
    if ok w then pick st ((part w l).getLast?.map Prod.snd) acc else acc) none

/-- The substitute reads only the parts of writers the reader may read. -/
theorem newest_congr (st : M → Nat) (ok : W → Bool) (ws : List W) (l₁ l₂ : List (W × M))
    (h : ∀ w, ok w = true → part w l₁ = part w l₂) :
    newest st ok ws l₁ = newest st ok ws l₂ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [newest, List.foldr_cons] at ih ⊢
    cases hw : ok w
    · simpa using ih
    · simp only [ite_true, h w hw, ih]

/-- The newest entry of a location whose writer the reader may read, read off the
interleaved log. -/
def latest (ok : W → Bool) (l : List (W × M)) : Option M :=
  ((l.filter (fun e => ok e.1)).getLast?).map Prod.snd

/-- Per-writer parts do not fix the newest visible entry. Both logs have the same parts, as the
order between writers is lost, and their newest entries differ. -/
theorem latest_not_of_parts :
    ∃ l₁ l₂ : List (Bool × Nat), (∀ w, part w l₁ = part w l₂) ∧
      latest (fun _ => true) l₁ ≠ latest (fun _ => true) l₂ :=
  ⟨[(true, 1), (false, 2)], [(false, 2), (true, 1)], fun w => by cases w <;> rfl,
    by decide⟩

end Location

end Ir
