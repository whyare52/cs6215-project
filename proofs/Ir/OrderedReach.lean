import Ir.Check
import Ir.Ordering

/-!
# Ordered reachability with flow summaries

`Reach` ignores the schedule and treats every agent as a black box that may copy anything it
reads into anything it writes. A clear by a black box is allowed but never guaranteed, so no
sound analysis can rely on it.

A flow summary says more about an agent. For each turn and each output (a board or variable it
writes), `dep` lists the inputs the output may depend on, and `kills` lists boards the turn
surely overwrites. Honest behaviours must respect the summary (`Respects`). Plain code has an
exact summary. A node that resets a board with fixed content has empty `dep` and kills it, so
a clear is an ordinary turn of an agent with that summary. The black-box summary
(`Summary.blackBox`) depends on everything and kills nothing, and every behaviour respects it.

`reachSum` walks a fixed schedule turn by turn.
- An output of `x` is tainted if `x` is controlled or reads a tainted input in its `dep`.
- A board `x` surely overwrites, with content from untainted inputs, becomes untainted.
- Commits echo to every board their owner writes, so a tainted echoed or owned variable
  taints those boards.
- An agent that reads a tainted input in some `dep` at its turn is tainted from then on.

Main results.
- `reachSum_sound`. On a fixed schedule, an agent `reachSum` leaves untainted writes the same
  actions to every output under any two attacker attacks, for every behaviour respecting the
  summary. `boardSum_sound` and `varSum_sound` do the same for final boards and variables.
- `reachSum_reach`. `reachSum` taints only agents `Reach` reaches, for every summary and
  schedule.
- `reach_iff_exists`. Under the black-box summary, `Reach` is exactly the union of `reachSum`
  over all schedules. `Reach` is the schedule-free collapse of the ordered analysis.
- `taintAfter_finer`. A finer summary taints less.
-/

set_option linter.unusedSectionVars false

namespace Ir

/-- An input or output of a turn. -/
inductive Loc (Board Var : Type) where
  | board (b : Board)
  | var (v : Var)
  deriving DecidableEq

def Universe.locs {Agent Board Var : Type} (U : Universe Agent Board Var) :
    List (Loc Board Var) :=
  U.boards.map .board ++ U.vars.map .var

theorem Universe.mem_locs {Agent Board Var : Type} (U : Universe Agent Board Var)
    (i : Loc Board Var) : i ∈ U.locs := by
  cases i with
  | board b => simp [Universe.locs, U.hB]
  | var v => simp [Universe.locs, U.hV]

/-- What a turn may depend on and what it surely overwrites. `dep x n o i` says output `o` of
`x`'s turn at index `n` may depend on input `i`. `kills x n b` says that turn surely replaces
board `b`. -/
structure Summary (Agent Board Var : Type) where
  dep : Agent → Nat → Loc Board Var → Loc Board Var → Bool
  kills : Agent → Nat → Board → Bool

/-- The black-box summary. Every output may depend on every input, and nothing is killed. -/
def Summary.blackBox {Agent Board Var : Type} : Summary Agent Board Var :=
  ⟨fun _ _ _ _ => true, fun _ _ _ => false⟩

/-- `S'` is at least as precise as `S`. -/
def Summary.Finer {Agent Board Var : Type} (S' S : Summary Agent Board Var) : Prop :=
  (∀ x n o i, S'.dep x n o i = true → S.dep x n o i = true) ∧
    ∀ x n b, S.kills x n b = true → S'.kills x n b = true

theorem Summary.finer_blackBox {Agent Board Var : Type} (S : Summary Agent Board Var) :
    S.Finer Summary.blackBox :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ h => by simp [Summary.blackBox] at h⟩

/-- Which boards, variables and agents may carry attacker influence. -/
structure Taint (Agent Board Var : Type) where
  board : Board → Bool
  var : Var → Bool
  agent : Agent → Bool

/-- `T'` taints at least what `T` does. -/
def Taint.Le {Agent Board Var : Type} (T T' : Taint Agent Board Var) : Prop :=
  (∀ b, T.board b = true → T'.board b = true) ∧ (∀ v, T.var v = true → T'.var v = true) ∧
    ∀ a, T.agent a = true → T'.agent a = true

theorem Taint.Le.refl {Agent Board Var : Type} (T : Taint Agent Board Var) : T.Le T :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem Taint.Le.trans {Agent Board Var : Type} {T₁ T₂ T₃ : Taint Agent Board Var}
    (h₁ : T₁.Le T₂) (h₂ : T₂.Le T₃) : T₁.Le T₃ :=
  ⟨fun b h => h₂.1 b (h₁.1 b h), fun v h => h₂.2.1 v (h₁.2.1 v h),
    fun a h => h₂.2.2 a (h₁.2.2 a h)⟩

theorem Bool.of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by cases b <;> simp_all

section

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]

/-- Whether an action can change location `o`. Every commit echoes, so it touches every
board. -/
def Action.touches : Loc Board Var → Action Board Var Val Msg → Bool
  | .board b, .post b' _ => decide (b' = b)
  | .board b, .replace b' _ => decide (b' = b)
  | .board _, .attend _ _ => true
  | .var v, .attend v' _ => decide (v' = v)
  | _, _ => false

/-- Two states hold the same value at a location. -/
def LocAgree : Loc Board Var → State Agent Board Var Val Msg →
    State Agent Board Var Val Msg → Prop
  | .board b, s₁, s₂ => s₁.logs b = s₂.logs b
  | .var v, s₁, s₂ => s₁.assign v = s₂.assign v

/-- The honest behaviour respects the summary. Views that agree on the inputs of `o` give the same
actions on `o`, and a killed board is always replaced. -/
structure Respects (S : Summary Agent Board Var) (honest : Behaviour Agent Board Var Val Msg) :
    Prop where
  dep : ∀ x n o (s₁ s₂ : State Agent Board Var Val Msg),
    (∀ i, S.dep x n o i = true → LocAgree i s₁ s₂) →
      (honest x n s₁).filter (Action.touches o) = (honest x n s₂).filter (Action.touches o)
  kills : ∀ x n b (s : State Agent Board Var Val Msg), S.kills x n b = true →
    ∃ m, Action.replace b m ∈ honest x n s

/-- Every behaviour respects the black-box summary, so the default instance assumes nothing. -/
theorem respects_blackBox (honest : Behaviour Agent Board Var Val Msg) :
    Respects Summary.blackBox honest where
  dep x n o s₁ s₂ h := by
    have hl : s₁.logs = s₂.logs := funext fun b => h (.board b) rfl
    have ha : s₁.assign = s₂.assign := funext fun v => h (.var v) rfl
    have : s₁ = s₂ := by cases s₁; cases s₂; simp_all
    rw [this]
  kills _ _ _ _ h := by simp [Summary.blackBox] at h

variable (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (U : Universe Agent Board Var) (S : Summary Agent Board Var)

/-! ## The analysis -/

/-- Input `i` is readable by `x` and tainted. -/
def readT (T : Taint Agent Board Var) (x : Agent) : Loc Board Var → Bool
  | .board b => cfg.reader b x && T.board b
  | .var v => cfg.sees x v && T.var v

/-- Some input of output `o` is readable and tainted. -/
def inT (T : Taint Agent Board Var) (x : Agent) (n : Nat) (o : Loc Board Var) : Bool :=
  U.locs.any fun i => S.dep x n o i && readT cfg T x i

/-- Output `o` of `x`'s turn may differ between runs because of its inputs or the attacker. -/
def hot (T : Taint Agent Board Var) (x : Agent) (n : Nat) (o : Loc Board Var) : Bool :=
  A.controls x || inT cfg U S T x n o

/-- `x` owns some variable, so it may commit and echo. -/
def ownsVar (x : Agent) : Bool :=
  U.vars.any fun w => decide (cfg.owner w = x)

/-- An echoed variable, or one `x` owns, is tainted, so `x`'s echoes may differ. -/
def echoBad (T : Taint Agent Board Var) (x : Agent) : Bool :=
  U.vars.any fun v => (cfg.echoSees v || decide (cfg.owner v = x)) && T.var v

/-- A turn of `x` at index `n`. -/
def agentT (x : Agent) (n : Nat) (T : Taint Agent Board Var) : Taint Agent Board Var where
  board b :=
    if cfg.writer b x then
      hot cfg A U S T x n (.board b) || (T.board b && !S.kills x n b) ||
        (ownsVar cfg U x && echoBad cfg U T x)
    else T.board b
  var v := if cfg.owner v = x then hot cfg A U S T x n (.var v) || T.var v else T.var v
  agent a := T.agent a ||
    (decide (a = x) && (A.controls x || U.locs.any fun o => inT cfg U S T x n o))

def sysT (T : Taint Agent Board Var) : Taint Agent Board Var :=
  { T with board := fun b => T.board b || A.injects b }

def turnT (n : Nat) : Turn Agent → Taint Agent Board Var → Taint Agent Board Var
  | .agent x, T => agentT cfg A U S x n T
  | .sys, T => sysT A T

def taintAfter : List (Turn Agent) → Taint Agent Board Var → Nat → Taint Agent Board Var
  | [], T, _ => T
  | t :: ts, T, n => taintAfter ts (turnT cfg A U S n t T) (n + 1)

/-- Both runs start in the same state. Only controlled agents are tainted. -/
def Taint.init : Taint Agent Board Var :=
  { board := fun _ => false, var := fun _ => false, agent := A.controls }

/-- Agent `a` may carry attacker influence after schedule `sched`. -/
def reachSum (sched : List (Turn Agent)) (a : Agent) : Bool :=
  (taintAfter cfg A U S sched (Taint.init A) 0).agent a

/-- Board `b` may carry attacker influence after schedule `sched`. -/
def boardSum (sched : List (Turn Agent)) (b : Board) : Bool :=
  (taintAfter cfg A U S sched (Taint.init A) 0).board b

def varSum (sched : List (Turn Agent)) (v : Var) : Bool :=
  (taintAfter cfg A U S sched (Taint.init A) 0).var v

theorem taintAfter_append (ts₁ ts₂ : List (Turn Agent)) (T : Taint Agent Board Var) (n : Nat) :
    taintAfter cfg A U S (ts₁ ++ ts₂) T n =
      taintAfter cfg A U S ts₂ (taintAfter cfg A U S ts₁ T n) (n + ts₁.length) := by
  induction ts₁ generalizing T n with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.cons_append, taintAfter, ih, List.length_cons]
    congr 1; omega

/-- Schedule-free reasoning. If every block the runtime may run preserves an invariant of the
taint state, so does every sequence of such blocks. -/
theorem taintAfter_blocks (Inv : Taint Agent Board Var → Prop) (Ok : List (Turn Agent) → Prop)
    (hb : ∀ blk, Ok blk → ∀ T n, Inv T → Inv (taintAfter cfg A U S blk T n)) :
    ∀ (blocks : List (List (Turn Agent))), (∀ blk ∈ blocks, Ok blk) →
      ∀ T n, Inv T → Inv (taintAfter cfg A U S blocks.flatten T n)
  | [], _, _, _, h => h
  | blk :: blks, hok, T, n, h => by
    rw [List.flatten_cons, taintAfter_append]
    exact taintAfter_blocks Inv Ok hb blks (fun b hm => hok b (List.mem_cons_of_mem _ hm)) _ _
      (hb blk (hok blk List.mem_cons_self) T n h)

/-! ## Agent taint only grows -/

theorem turnT_agent_mono (n : Nat) (t : Turn Agent) (T : Taint Agent Board Var)
    (a : Agent) (h : T.agent a = true) : (turnT cfg A U S n t T).agent a = true := by
  cases t with
  | agent x => simp [turnT, agentT, h]
  | sys => exact h

theorem taintAfter_agent_mono :
    ∀ (ts : List (Turn Agent)) (T : Taint Agent Board Var) (n : Nat) (a : Agent),
      T.agent a = true → (taintAfter cfg A U S ts T n).agent a = true
  | [], _, _, _, h => h
  | t :: ts, T, n, a, h =>
    taintAfter_agent_mono ts _ _ a (turnT_agent_mono cfg A U S n t T a h)

end

/-! ## Projections of a turn onto one location -/

section

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg} {x : Agent}

theorem performAll_congr (E : State Agent Board Var Val Msg → State Agent Board Var Val Msg → Prop)
    (hE : ∀ act s s', E s s' → E (perform cfg x act s) (perform cfg x act s')) :
    ∀ (acts : List (Action Board Var Val Msg)) s s', E s s' →
      E (performAll cfg x acts s) (performAll cfg x acts s')
  | [], _, _, h => h
  | act :: acts, _, _, h => performAll_congr E hE acts _ _ (hE act _ _ h)

/-- If a location's value depends only on itself and is left alone by the actions that do not
touch it, a turn's effect on it is the effect of its touching actions alone. -/
theorem performAll_filter
    (E : State Agent Board Var Val Msg → State Agent Board Var Val Msg → Prop)
    (p : Action Board Var Val Msg → Bool) (hrefl : ∀ s, E s s)
    (htrans : ∀ s₁ s₂ s₃, E s₁ s₂ → E s₂ s₃ → E s₁ s₃)
    (hE : ∀ act s s', E s s' → E (perform cfg x act s) (perform cfg x act s'))
    (hskip : ∀ act s, p act = false → E (perform cfg x act s) s) :
    ∀ (acts : List (Action Board Var Val Msg)) s,
      E (performAll cfg x acts s) (performAll cfg x (acts.filter p) s)
  | [], s => hrefl s
  | act :: acts, s => by
    cases hp : p act with
    | true =>
      simp only [performAll, List.filter_cons, hp, ite_true]
      exact performAll_filter E p hrefl htrans hE hskip acts _
    | false =>
      simp only [performAll, List.filter_cons, hp]
      exact htrans _ _ _ (performAll_filter E p hrefl htrans hE hskip acts _)
        (performAll_congr E hE _ _ _ (hskip act s hp))

theorem perform_board_congr (b : Board) (act : Action Board Var Val Msg)
    {s s' : State Agent Board Var Val Msg} (h : s.logs b = s'.logs b ∧ s.assign = s'.assign) :
    (perform cfg x act s).logs b = (perform cfg x act s').logs b ∧
      (perform cfg x act s).assign = (perform cfg x act s').assign := by
  obtain ⟨hl, ha⟩ := h
  cases act with
  | post b' m =>
    simp only [perform]
    split
    · refine ⟨?_, ha⟩
      simp only [post]
      split
      · subst_vars; rw [hl]
      · exact hl
    · exact ⟨hl, ha⟩
  | replace b' m =>
    simp only [perform]
    split
    · refine ⟨?_, ha⟩
      simp only [setLog]
      split
      · rfl
      · exact hl
    · exact ⟨hl, ha⟩
  | attend v t =>
    simp only [perform]
    rw [ha]
    split
    · simp only [commit]
      rw [hl, ha]
      exact ⟨rfl, rfl⟩
    · exact ⟨hl, ha⟩
  | skip => exact ⟨hl, ha⟩

theorem perform_board_skip (b : Board) (act : Action Board Var Val Msg)
    (s : State Agent Board Var Val Msg) (hp : Action.touches (.board b) act = false) :
    (perform cfg x act s).logs b = s.logs b ∧ (perform cfg x act s).assign = s.assign := by
  cases act with
  | post b' m =>
    simp only [Action.touches, decide_eq_false_iff_not] at hp
    simp only [perform]
    split
    · simp [post, Ne.symm hp]
    · exact ⟨rfl, rfl⟩
  | replace b' m =>
    simp only [Action.touches, decide_eq_false_iff_not] at hp
    simp only [perform]
    split
    · simp [setLog, Ne.symm hp]
    · exact ⟨rfl, rfl⟩
  | attend => simp [Action.touches] at hp
  | skip => exact ⟨rfl, rfl⟩

/-- A board's log after a turn is fixed by its log before, the assignment, and the actions
touching it. -/
theorem performAll_board_filter (b : Board) (acts : List (Action Board Var Val Msg))
    (s : State Agent Board Var Val Msg) :
    (performAll cfg x acts s).logs b =
      (performAll cfg x (acts.filter (Action.touches (.board b))) s).logs b :=
  (performAll_filter (fun s s' => s.logs b = s'.logs b ∧ s.assign = s'.assign) _
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩)
    (fun act _ _ h => perform_board_congr b act h)
    (fun act s hp => perform_board_skip b act s hp) acts s).1

theorem attend_assign_ne {v v' : Var} {t : Val} (hne : v ≠ v')
    (s : State Agent Board Var Val Msg) :
    (perform cfg x (.attend v' t) s).assign v = s.assign v := by
  simp only [perform]
  split
  · simp [commit, hne]
  · rfl

theorem perform_var_congr (v : Var) (act : Action Board Var Val Msg)
    {s s' : State Agent Board Var Val Msg} (h : s.assign v = s'.assign v) :
    (perform cfg x act s).assign v = (perform cfg x act s').assign v := by
  cases act with
  | post b m => simp only [perform]; split <;> exact h
  | replace b m => simp only [perform]; split <;> exact h
  | attend v' t =>
    by_cases hv : v = v'
    · subst hv
      simp only [perform, h]
      split
      · simp [commit]
      · exact h
    · rw [attend_assign_ne hv, attend_assign_ne hv]; exact h
  | skip => exact h

theorem perform_var_skip (v : Var) (act : Action Board Var Val Msg)
    (s : State Agent Board Var Val Msg) (hp : Action.touches (.var v) act = false) :
    (perform cfg x act s).assign v = s.assign v := by
  cases act with
  | post b m => simp only [perform]; split <;> rfl
  | replace b m => simp only [perform]; split <;> rfl
  | attend v' t =>
    simp only [Action.touches, decide_eq_false_iff_not] at hp
    exact attend_assign_ne (Ne.symm hp) s
  | skip => rfl

theorem performAll_var_filter (v : Var) (acts : List (Action Board Var Val Msg))
    (s : State Agent Board Var Val Msg) :
    (performAll cfg x acts s).assign v =
      (performAll cfg x (acts.filter (Action.touches (.var v))) s).assign v :=
  performAll_filter (fun s s' => s.assign v = s'.assign v) _ (fun _ => rfl)
    (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun act _ _ h => perform_var_congr v act h)
    (fun act s hp => perform_var_skip v act s hp) acts s

theorem performAll_logs_nowrite {b : Board} (hb : cfg.writer b x = false) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      (performAll cfg x acts s).logs b = s.logs b
  | [], _ => rfl
  | act :: acts, s => by
    simp only [performAll]
    rw [performAll_logs_nowrite hb acts]
    cases act with
    | post b' m =>
      simp only [perform]
      split
      · simp only [post]
        split
        · subst_vars; simp_all
        · rfl
      · rfl
    | replace b' m =>
      simp only [perform]
      split
      · simp only [setLog]
        split
        · subst_vars; simp_all
        · rfl
      · rfl
    | attend v t =>
      simp only [perform]
      split
      · simp [commit, hb]
      · rfl
    | skip => rfl

/-- Two runs agree on every variable whose commit by `x` could change an echo, provided `x`
owns some variable at all. -/
def EchoAgree (cfg : Config Agent Board Var Val Msg) (x : Agent)
    (s₁ s₂ : State Agent Board Var Val Msg) : Prop :=
  ∀ v, cfg.owner v = x → ∀ v', (cfg.echoSees v' = true ∨ cfg.owner v' = x) →
    s₁.assign v' = s₂.assign v'

theorem perform_echoAgree (act : Action Board Var Val Msg)
    {s₁ s₂ : State Agent Board Var Val Msg} (h : EchoAgree cfg x s₁ s₂) :
    EchoAgree cfg x (perform cfg x act s₁) (perform cfg x act s₂) := by
  intro w hw v' hv'
  cases act with
  | post b m => simp only [perform]; split <;> exact h w hw v' hv'
  | replace b m => simp only [perform]; split <;> exact h w hw v' hv'
  | attend v t =>
    by_cases ho : cfg.owner v = x
    · have hv : s₁.assign v = s₂.assign v := h w hw v (Or.inr ho)
      simp only [perform, ho, true_and, hv]
      split
      · simp only [commit]
        split
        · rfl
        · exact h w hw v' hv'
      · exact h w hw v' hv'
    · simp only [perform, ho, false_and, ↓reduceIte]
      exact h w hw v' hv'
  | skip => exact h w hw v' hv'

theorem perform_board_same (b : Board) (act : Action Board Var Val Msg)
    {s₁ s₂ : State Agent Board Var Val Msg} (he : EchoAgree cfg x s₁ s₂)
    (hl : s₁.logs b = s₂.logs b) :
    (perform cfg x act s₁).logs b = (perform cfg x act s₂).logs b := by
  cases act with
  | post b' m =>
    simp only [perform]
    split
    · simp only [post]
      split
      · subst_vars; rw [hl]
      · exact hl
    · exact hl
  | replace b' m =>
    simp only [perform]
    split
    · simp only [setLog]
      split
      · rfl
      · exact hl
    · exact hl
  | attend v t =>
    by_cases ho : cfg.owner v = x
    · have hv : s₁.assign v = s₂.assign v := he v ho v (Or.inr ho)
      simp only [perform, ho, true_and, hv]
      split
      · simp only [commit]
        split
        · rw [hl]
          congr 3
          congr 1
          funext v'
          split
          · split
            · rfl
            · exact he v ho v' (Or.inl (by assumption))
          · rfl
        · exact hl
      · exact hl
    · simp only [perform, ho, false_and, ↓reduceIte]
      exact hl
  | skip => exact hl

/-- Running the same touching actions on both sides. A killed board ends equal even if it
started different. -/
theorem performAll_board_same (b : Board) (hw : cfg.writer b x = true) :
    ∀ (L : List (Action Board Var Val Msg)) {s₁ s₂ : State Agent Board Var Val Msg},
      EchoAgree cfg x s₁ s₂ → (s₁.logs b = s₂.logs b ∨ ∃ m, Action.replace b m ∈ L) →
      (performAll cfg x L s₁).logs b = (performAll cfg x L s₂).logs b
  | [], _, _, _, h => by
    rcases h with h | ⟨_, hm⟩
    · exact h
    · simp at hm
  | act :: acts, s₁, s₂, he, h => by
    simp only [performAll]
    refine performAll_board_same b hw acts (perform_echoAgree act he) ?_
    rcases h with h | ⟨m, hm⟩
    · exact Or.inl (perform_board_same b act he h)
    · rcases List.mem_cons.1 hm with hm | hm
      · subst hm
        left
        simp only [perform, hw, ↓reduceIte, setLog]
      · exact Or.inr ⟨m, hm⟩

end

/-! ## Soundness -/

section

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  {cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
  {U : Universe Agent Board Var} {S : Summary Agent Board Var}

/-- Two states agree on every untainted board and variable. The taint state changes along the
run, so this agreement is indexed by time. -/
def TAgree (T : Taint Agent Board Var) (s₁ s₂ : State Agent Board Var Val Msg) : Prop :=
  (∀ b, T.board b = false → s₁.logs b = s₂.logs b) ∧
    ∀ v, T.var v = false → s₁.assign v = s₂.assign v

theorem TAgree.refl (T : Taint Agent Board Var) (s : State Agent Board Var Val Msg) :
    TAgree T s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem TAgree.symm {T : Taint Agent Board Var} {s₁ s₂ : State Agent Board Var Val Msg}
    (h : TAgree T s₁ s₂) : TAgree T s₂ s₁ :=
  ⟨fun b hb => (h.1 b hb).symm, fun v hv => (h.2 v hv).symm⟩

theorem TAgree.mono {T T' : Taint Agent Board Var} {s₁ s₂ : State Agent Board Var Val Msg}
    (hle : T.Le T') (h : TAgree T s₁ s₂) : TAgree T' s₁ s₂ := by
  refine ⟨fun b hb => h.1 b ?_, fun v hv => h.2 v ?_⟩
  · exact Bool.of_ne_true fun ht => by simp [hle.1 b ht] at hb
  · exact Bool.of_ne_true fun ht => by simp [hle.2.1 v ht] at hv

/-- An untainted input of `x` is the same in both views. -/
theorem locAgree_view {T : Taint Agent Board Var} {x : Agent} {i : Loc Board Var}
    {s₁ s₂ : State Agent Board Var Val Msg} (h : TAgree T s₁ s₂)
    (hi : readT cfg T x i = false) : LocAgree i (view cfg x s₁) (view cfg x s₂) := by
  cases i with
  | board b =>
    simp only [LocAgree, view]
    cases hr : cfg.reader b x with
    | false => rfl
    | true =>
      simp only [readT, hr, Bool.true_and] at hi
      simp [h.1 b hi]
  | var v =>
    simp only [LocAgree, view]
    cases hs : cfg.sees x v with
    | false => rfl
    | true =>
      simp only [readT, hs, Bool.true_and] at hi
      simp [h.2 v hi]

theorem inT_false {T : Taint Agent Board Var} {x : Agent} {n : Nat} {o : Loc Board Var}
    (h : inT cfg U S T x n o = false) :
    ∀ i, S.dep x n o i = true → readT cfg T x i = false := by
  intro i hd
  simp only [inT, List.any_eq_false, Bool.and_eq_true, not_and] at h
  exact Bool.of_ne_true (h i (U.mem_locs i) hd)

/-- One turn of `x`, given that untainted outputs get the same actions and killed boards are
replaced. -/
theorem tagree_agentT {T : Taint Agent Board Var} {x : Agent} {n : Nat}
    {acts₁ acts₂ : List (Action Board Var Val Msg)} {s₁ s₂ : State Agent Board Var Val Msg}
    (h : TAgree T s₁ s₂)
    (hfil : ∀ o, hot cfg A U S T x n o = false →
      acts₁.filter (Action.touches o) = acts₂.filter (Action.touches o))
    (hkill : ∀ b, S.kills x n b = true → hot cfg A U S T x n (.board b) = false →
      ∃ m, Action.replace b m ∈ acts₁) :
    TAgree (agentT cfg A U S x n T) (performAll cfg x acts₁ s₁) (performAll cfg x acts₂ s₂) := by
  refine ⟨fun b hb => ?_, fun v hv => ?_⟩
  · cases hw : cfg.writer b x with
    | false =>
      simp only [agentT, hw] at hb
      rw [performAll_logs_nowrite hw, performAll_logs_nowrite hw]
      exact h.1 b (by simpa using hb)
    | true =>
      simp only [agentT, hw, ↓reduceIte, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
        Bool.not_eq_false'] at hb
      obtain ⟨⟨hhot, hold⟩, hecho⟩ := hb
      rw [performAll_board_filter b acts₁, performAll_board_filter b acts₂, hfil _ hhot]
      refine performAll_board_same b hw _ ?_ ?_
      · intro w hw' v' hv'
        rcases hecho with ho | he
        · simp only [ownsVar, List.any_eq_false, decide_eq_true_eq] at ho
          exact absurd hw' (ho w (U.hV w))
        · simp only [echoBad, List.any_eq_false, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq, not_and] at he
          exact h.2 v' (Bool.of_ne_true (he v' (U.hV v') hv'))
      · rcases hold with ho | hk
        · exact Or.inl (h.1 b ho)
        · obtain ⟨m, hm⟩ := hkill b hk hhot
          rw [← hfil _ hhot]
          exact Or.inr ⟨m, List.mem_filter.2 ⟨hm, by simp [Action.touches]⟩⟩
  · by_cases ho : cfg.owner v = x
    · simp only [agentT, ho, ↓reduceIte, Bool.or_eq_false_iff] at hv
      rw [performAll_var_filter v acts₁, performAll_var_filter v acts₂, hfil _ hv.1]
      exact performAll_congr (fun s s' => s.assign v = s'.assign v)
        (fun act _ _ h => perform_var_congr v act h) _ _ _ (h.2 v hv.2)
    · simp only [agentT, ho, ↓reduceIte] at hv
      rw [performAll_assign cfg (Ne.symm ho), performAll_assign cfg (Ne.symm ho)]
      exact h.2 v hv

theorem tagree_sysT {T : Taint Agent Board Var} {adv : Attack Agent Board Var Val Msg}
    {n : Nat} {s s' : State Agent Board Var Val Msg} (h : TAgree (sysT A T) s s') :
    TAgree (sysT A T) (sysStep A adv n s) s' := by
  unfold sysStep
  split
  · split
    · refine ⟨fun b' hb' => ?_, h.2⟩
      simp only [post]
      split
      · subst_vars; simp_all [sysT]
      · exact h.1 b' hb'
    · exact h
  · exact h

/-- Unwinding with time-indexed agreement. Each turn maps agreement under `T` to agreement
under the taint state the analysis computes for the next instant. -/
theorem tagree_step {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest)
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} (n : Nat) (t : Turn Agent)
    {T : Taint Agent Board Var} {s₁ s₂ : State Agent Board Var Val Msg} (h : TAgree T s₁ s₂) :
    TAgree (turnT cfg A U S n t T) (step cfg A honest adv₁ n t s₁)
      (step cfg A honest adv₂ n t s₂) := by
  cases t with
  | agent x =>
    simp only [turnT, step]
    cases hc : A.controls x with
    | true =>
      exact tagree_agentT h (fun o ho => by simp [hot, hc] at ho)
        (fun b _ ho => by simp [hot, hc] at ho)
    | false =>
      simp only [choose, hc, Bool.false_eq_true, ↓reduceIte]
      refine tagree_agentT h (fun o ho => ?_) (fun b hk _ => hR.kills x n b _ hk)
      simp only [hot, hc, Bool.false_or] at ho
      exact hR.dep x n o _ _ fun i hd => locAgree_view h (inT_false ho i hd)
  | sys =>
    simp only [turnT, step]
    have hle : T.Le (sysT A T) := ⟨fun b hb => by simp [sysT, hb], fun _ h => h, fun _ h => h⟩
    exact (tagree_sysT (tagree_sysT (h.mono hle)).symm).symm

theorem tagree_run {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest)
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} :
    ∀ (sched : List (Turn Agent)) {n : Nat} {T : Taint Agent Board Var}
      {s₁ s₂ : State Agent Board Var Val Msg}, TAgree T s₁ s₂ →
      TAgree (taintAfter cfg A U S sched T n) (run cfg A honest adv₁ sched s₁ n)
        (run cfg A honest adv₂ sched s₂ n)
  | [], _, _, _, _, h => h
  | t :: ts, n, _, _, _, h => tagree_run hR ts (tagree_step hR n t h)

theorem actionsOf_filter_eq {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest)
    {adv₁ adv₂ : Attack Agent Board Var Val Msg} {a : Agent} (o : Loc Board Var) :
    ∀ (sched : List (Turn Agent)) {n : Nat} {T : Taint Agent Board Var}
      {s₁ s₂ : State Agent Board Var Val Msg}, TAgree T s₁ s₂ →
      (taintAfter cfg A U S sched T n).agent a = false →
      (actionsOf cfg A honest adv₁ a sched s₁ n).map (List.filter (Action.touches o)) =
        (actionsOf cfg A honest adv₂ a sched s₂ n).map (List.filter (Action.touches o))
  | [], _, _, _, _, _, _ => rfl
  | t :: ts, n, T, s₁, s₂, h, ha => by
    simp only [actionsOf, List.map_append]
    congr 1
    · cases t with
      | agent x =>
        simp only
        split
        · rename_i hxa
          cases hxa
          have hfin : (turnT cfg A U S n (.agent a) T).agent a = false :=
            Bool.of_ne_true fun ht => by
              have := taintAfter_agent_mono cfg A U S ts _ (n + 1) a ht
              simp only [taintAfter] at ha; rw [ha] at this; exact Bool.noConfusion this
          simp only [turnT, agentT, decide_true, Bool.true_and, Bool.or_eq_false_iff,
            List.any_eq_false] at hfin
          obtain ⟨_, hc, hin⟩ := hfin
          have ho : inT cfg U S T a n o = false := Bool.of_ne_true (hin o (U.mem_locs o))
          simp only [choose, hc, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil,
            List.cons.injEq, and_true]
          exact hR.dep a n o _ _ fun i hd => locAgree_view h (inT_false ho i hd)
        · rfl
      | sys => rfl
    · exact actionsOf_filter_eq hR o ts (tagree_step hR n t h) ha

/-- Soundness. On a fixed schedule, an agent `reachSum` leaves untainted writes the same
actions to every output under any two attacker attacks, for every behaviour that respects the
summary. Actions on different outputs commute up to echoes, so these projections fix the
agent's whole effect on the state. -/
theorem reachSum_sound {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) (a : Agent) (ha : reachSum cfg A U S sched a = false)
    (o : Loc Board Var) :
    (actionsOf cfg A honest adv₁ a sched s₀).map (List.filter (Action.touches o)) =
      (actionsOf cfg A honest adv₂ a sched s₀).map (List.filter (Action.touches o)) :=
  actionsOf_filter_eq hR o sched (TAgree.refl _ s₀) ha

/-- A board `boardSum` leaves untainted ends with the same log. -/
theorem boardSum_sound {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) (b : Board) (hb : boardSum cfg A U S sched b = false) :
    (run cfg A honest adv₁ sched s₀).logs b = (run cfg A honest adv₂ sched s₀).logs b :=
  (tagree_run hR sched (TAgree.refl _ s₀)).1 b hb

theorem varSum_sound {honest : Behaviour Agent Board Var Val Msg} (hR : Respects S honest)
    (adv₁ adv₂ : Attack Agent Board Var Val Msg) (s₀ : State Agent Board Var Val Msg)
    (sched : List (Turn Agent)) (v : Var) (hv : varSum cfg A U S sched v = false) :
    (run cfg A honest adv₁ sched s₀).assign v = (run cfg A honest adv₂ sched s₀).assign v :=
  (tagree_run hR sched (TAgree.refl _ s₀)).2 v hv

/-! ## Precision against `Reach` -/

/-- Every tainted agent and variable owner is reachable, and so is every reader of a tainted
board. -/
def ReachInv (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (T : Taint Agent Board Var) : Prop :=
  (∀ a, T.agent a = true → Reach cfg A a) ∧
    (∀ b y, T.board b = true → cfg.reader b y = true → Reach cfg A y) ∧
    ∀ v, T.var v = true → Reach cfg A (cfg.owner v)

theorem reach_of_inT {T : Taint Agent Board Var} (hi : ReachInv cfg A T) {x : Agent} {n : Nat}
    {o : Loc Board Var} (h : inT cfg U S T x n o = true) : Reach cfg A x := by
  simp only [inT, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨i, _, _, hr⟩ := h
  cases i with
  | board b =>
    simp only [readT, Bool.and_eq_true] at hr
    exact hi.2.1 b x hr.2 hr.1
  | var v =>
    simp only [readT, Bool.and_eq_true] at hr
    exact Reach.sees (hi.2.2 v hr.2) hr.1

theorem reach_of_hot {T : Taint Agent Board Var} (hi : ReachInv cfg A T) {x : Agent} {n : Nat}
    {o : Loc Board Var} (h : hot cfg A U S T x n o = true) : Reach cfg A x := by
  simp only [hot, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Reach.ctrl h
  · exact reach_of_inT hi h

theorem reachInv_turnT (n : Nat) (t : Turn Agent) {T : Taint Agent Board Var}
    (hi : ReachInv cfg A T) : ReachInv cfg A (turnT cfg A U S n t T) := by
  cases t with
  | agent x =>
    refine ⟨fun a ha => ?_, fun b y hb hy => ?_, fun v hv => ?_⟩
    · simp only [turnT, agentT, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true] at ha
      rcases ha with ha | ⟨rfl, hc | ⟨o, _, ho⟩⟩
      · exact hi.1 a ha
      · exact Reach.ctrl hc
      · exact reach_of_inT hi ho
    · simp only [turnT, agentT] at hb
      split at hb
      · rename_i hw
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hb
        rcases hb with (hh | ⟨hb, _⟩) | ⟨ho, he⟩
        · exact Reach.board (reach_of_hot hi hh) hw hy
        · exact hi.2.1 b y hb hy
        · simp only [ownsVar, List.any_eq_true, decide_eq_true_eq] at ho
          obtain ⟨w, _, hwx⟩ := ho
          simp only [echoBad, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true,
            decide_eq_true_eq] at he
          obtain ⟨v, _, hev | hov, htv⟩ := he
          · exact Reach.echo (w := w) (hi.2.2 v htv) hev (by rw [hwx]; exact hw) hy
          · exact Reach.board (hov ▸ hi.2.2 v htv) hw hy
      · exact hi.2.1 b y hb hy
    · simp only [turnT, agentT] at hv
      split at hv
      · rename_i ho
        simp only [Bool.or_eq_true] at hv
        rcases hv with hh | hv
        · rw [ho]; exact reach_of_hot hi hh
        · exact hi.2.2 v hv
      · exact hi.2.2 v hv
  | sys =>
    refine ⟨hi.1, fun b y hb hy => ?_, hi.2.2⟩
    simp only [turnT, sysT, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hi.2.1 b y hb hy
    · exact Reach.inj hb hy

theorem reachInv_taintAfter :
    ∀ (sched : List (Turn Agent)) {T : Taint Agent Board Var} {n : Nat},
      ReachInv cfg A T → ReachInv cfg A (taintAfter cfg A U S sched T n)
  | [], _, _, h => h
  | t :: ts, _, n, h => reachInv_taintAfter ts (reachInv_turnT n t h)

theorem reachInv_init : ReachInv cfg A (Taint.init (Board := Board) (Var := Var) A) :=
  ⟨fun _ ha => Reach.ctrl ha, fun _ _ hb _ => by simp [Taint.init] at hb,
    fun _ hv => by simp [Taint.init] at hv⟩

/-- The ordered analysis is at least as precise as `Reach`, for every summary and every
schedule. -/
theorem reachSum_reach (sched : List (Turn Agent)) {a : Agent}
    (h : reachSum cfg A U S sched a = true) : Reach cfg A a :=
  (reachInv_taintAfter (U := U) (S := S) sched reachInv_init).1 a h

/-! ## Black-box summaries recover `Reach` -/

/-- An agent that is tainted can still name the input that tainted it. -/
def Witness (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (U : Universe Agent Board Var) (T : Taint Agent Board Var) : Prop :=
  ∀ x, T.agent x = true → A.controls x = true ∨ ∃ i ∈ U.locs, readT cfg T x i = true

theorem readT_mono {T T' : Taint Agent Board Var} (hle : T.Le T') {x : Agent}
    {i : Loc Board Var} (h : readT cfg T x i = true) : readT cfg T' x i = true := by
  cases i with
  | board b =>
    simp only [readT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, hle.1 b h.2⟩
  | var v =>
    simp only [readT, Bool.and_eq_true] at h ⊢; exact ⟨h.1, hle.2.1 v h.2⟩

/-- Without kills, taint only grows. -/
theorem turnT_le_blackBox (n : Nat) (t : Turn Agent) (T : Taint Agent Board Var) :
    T.Le (turnT cfg A U Summary.blackBox n t T) := by
  cases t with
  | agent x =>
    refine ⟨fun b hb => ?_, fun v hv => ?_, fun a ha => by simp [turnT, agentT, ha]⟩
    · simp only [turnT, agentT]; split <;> simp [hb, Summary.blackBox]
    · simp only [turnT, agentT]; split <;> simp [hv]
  | sys => exact ⟨fun b hb => by simp [turnT, sysT, hb], fun _ h => h, fun _ h => h⟩

theorem taintAfter_le_blackBox :
    ∀ (ts : List (Turn Agent)) (T : Taint Agent Board Var) (n : Nat),
      T.Le (taintAfter cfg A U Summary.blackBox ts T n)
  | [], T, _ => Taint.Le.refl T
  | t :: ts, T, n =>
    (turnT_le_blackBox n t T).trans (taintAfter_le_blackBox ts _ _)

theorem witness_turnT (n : Nat) (t : Turn Agent) {T : Taint Agent Board Var}
    (hw : Witness cfg A U T) : Witness cfg A U (turnT cfg A U Summary.blackBox n t T) := by
  intro x hx
  have hle := turnT_le_blackBox (cfg := cfg) (A := A) (U := U) n t T
  cases t with
  | agent y =>
    simp only [turnT, agentT, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true] at hx
    rcases hx with hx | ⟨rfl, hc | ⟨o, _, ho⟩⟩
    · rcases hw x hx with hc | ⟨i, hi, hr⟩
      · exact Or.inl hc
      · exact Or.inr ⟨i, hi, readT_mono hle hr⟩
    · exact Or.inl hc
    · simp only [inT, List.any_eq_true, Bool.and_eq_true] at ho
      obtain ⟨i, hi, _, hr⟩ := ho
      exact Or.inr ⟨i, hi, readT_mono hle hr⟩
  | sys =>
    rcases hw x hx with hc | ⟨i, hi, hr⟩
    · exact Or.inl hc
    · exact Or.inr ⟨i, hi, readT_mono hle hr⟩

theorem witness_taintAfter :
    ∀ (ts : List (Turn Agent)) {T : Taint Agent Board Var} {n : Nat},
      Witness cfg A U T → Witness cfg A U (taintAfter cfg A U Summary.blackBox ts T n)
  | [], _, _, h => h
  | t :: ts, _, n, h => witness_taintAfter ts (witness_turnT n t h)

/-- A tainted black box taints every output at each later turn. -/
theorem hot_of_witness {T : Taint Agent Board Var} (hw : Witness cfg A U T) {x : Agent}
    (hx : T.agent x = true) (n : Nat) (o : Loc Board Var) :
    hot cfg A U Summary.blackBox T x n o = true := by
  simp only [hot, Bool.or_eq_true]
  rcases hw x hx with hc | ⟨i, hi, hr⟩
  · exact Or.inl hc
  · right
    simp only [inT, List.any_eq_true, Bool.and_eq_true]
    exact ⟨i, hi, rfl, hr⟩

theorem agent_of_readT {T : Taint Agent Board Var} {y : Agent} {n : Nat} {i : Loc Board Var}
    (h : readT cfg T y i = true) :
    (turnT cfg A U Summary.blackBox n (.agent y) T).agent y = true := by
  simp only [turnT, agentT, decide_true, Bool.true_and, Bool.or_eq_true, List.any_eq_true]
  right; right
  refine ⟨i, U.mem_locs i, ?_⟩
  simp only [inT, List.any_eq_true, Bool.and_eq_true]
  exact ⟨i, U.mem_locs i, rfl, h⟩

/-- Some schedule taints `a`, with a final state whose tainted agents have witnesses. -/
theorem exists_sched_of_reach {a : Agent} (h : Reach cfg A a) :
    ∃ sched : List (Turn Agent), reachSum cfg A U Summary.blackBox sched a = true := by
  have hwi : Witness cfg A U (Taint.init (Board := Board) (Var := Var) A) :=
    fun x hx => Or.inl hx
  have key : ∀ sched : List (Turn Agent),
      Witness cfg A U (taintAfter cfg A U Summary.blackBox sched (Taint.init A) 0) :=
    fun sched => witness_taintAfter sched hwi
  induction h with
  | ctrl hc => exact ⟨[], hc⟩
  | @inj b x hi hr =>
    refine ⟨[.sys, .agent x], ?_⟩
    simp only [reachSum, taintAfter]
    exact agent_of_readT (i := .board b) (by simp [readT, hr, turnT, sysT, hi])
  | @board b x y _ hw hr ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s ++ [.agent x, .agent y], ?_⟩
    simp only [reachSum, taintAfter_append, taintAfter, Nat.zero_add]
    apply agent_of_readT (i := .board b)
    have hh := hot_of_witness (key s) hs s.length (.board b)
    simp [readT, hr, turnT, agentT, hw, hh]
  | @sees v y _ hs ih =>
    obtain ⟨s, hs'⟩ := ih
    refine ⟨s ++ [.agent (cfg.owner v), .agent y], ?_⟩
    simp only [reachSum, taintAfter_append, taintAfter, Nat.zero_add]
    apply agent_of_readT (i := .var v)
    have hh := hot_of_witness (key s) hs' s.length (.var v)
    simp [readT, hs, turnT, agentT, hh]
  | @echo v w b y _ he hw hr ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s ++ [.agent (cfg.owner v), .agent (cfg.owner w), .agent y], ?_⟩
    simp only [reachSum, taintAfter_append, taintAfter, Nat.zero_add]
    apply agent_of_readT (i := .board b)
    have hh := hot_of_witness (key s) hs s.length (.var v)
    generalize hT₀ : taintAfter cfg A U Summary.blackBox s (Taint.init A) 0 = T₀ at hh ⊢
    generalize hT₁ : turnT cfg A U Summary.blackBox s.length (.agent (cfg.owner v)) T₀ = T₁
    have h₁ : T₁.var v = true := by rw [← hT₁]; simp [turnT, agentT, hh]
    have hown : ownsVar cfg U (cfg.owner w) = true := by
      simp only [ownsVar, List.any_eq_true, decide_eq_true_eq]; exact ⟨w, U.hV w, rfl⟩
    have hbad : echoBad cfg U T₁ (cfg.owner w) = true := by
      simp only [echoBad, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨v, U.hV v, Or.inl he, h₁⟩
    simp [readT, hr, turnT, agentT, hw, hown, hbad]

/-- Under the black-box summary, `Reach` is exactly the agents some schedule taints. -/
theorem reach_iff_exists {a : Agent} :
    Reach cfg A a ↔ ∃ sched : List (Turn Agent), reachSum cfg A U Summary.blackBox sched a = true :=
  ⟨exists_sched_of_reach, fun ⟨sched, h⟩ => reachSum_reach sched h⟩

/-! ## Finer summaries taint less -/

theorem readT_le {T T' : Taint Agent Board Var} (hle : T'.Le T) {x : Agent} {i : Loc Board Var}
    (h : readT cfg T' x i = true) : readT cfg T x i = true := readT_mono hle h

theorem inT_finer {S' : Summary Agent Board Var} (hS : S'.Finer S) {T T' : Taint Agent Board Var}
    (hle : T'.Le T) {x : Agent} {n : Nat} {o : Loc Board Var}
    (h : inT cfg U S' T' x n o = true) : inT cfg U S T x n o = true := by
  simp only [inT, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨i, hi, hd, hr⟩ := h
  exact ⟨i, hi, hS.1 _ _ _ _ hd, readT_le hle hr⟩

theorem hot_finer {S' : Summary Agent Board Var} (hS : S'.Finer S) {T T' : Taint Agent Board Var}
    (hle : T'.Le T) {x : Agent} {n : Nat} {o : Loc Board Var}
    (h : hot cfg A U S' T' x n o = true) : hot cfg A U S T x n o = true := by
  simp only [hot, Bool.or_eq_true] at h ⊢
  exact h.imp id (inT_finer hS hle)

theorem turnT_finer {S' : Summary Agent Board Var} (hS : S'.Finer S) (n : Nat) (t : Turn Agent)
    {T T' : Taint Agent Board Var} (hle : T'.Le T) :
    (turnT cfg A U S' n t T').Le (turnT cfg A U S n t T) := by
  cases t with
  | agent x =>
    refine ⟨fun b hb => ?_, fun v hv => ?_, fun a ha => ?_⟩
    · simp only [turnT, agentT] at hb ⊢
      split
      · rename_i hw
        simp only [hw, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hb ⊢
        rcases hb with (hh | ⟨hb, hk⟩) | ⟨ho, he⟩
        · exact Or.inl (Or.inl (hot_finer hS hle hh))
        · refine Or.inl (Or.inr ⟨hle.1 b hb, Bool.of_ne_true fun hk' => ?_⟩)
          simp [hS.2 _ _ _ hk'] at hk
        · refine Or.inr ⟨ho, ?_⟩
          simp only [echoBad, List.any_eq_true, Bool.and_eq_true] at he ⊢
          obtain ⟨v, hv, hev, htv⟩ := he
          exact ⟨v, hv, hev, hle.2.1 v htv⟩
      · rename_i hw
        simp only [hw] at hb
        exact hle.1 b (by simpa using hb)
    · simp only [turnT, agentT] at hv ⊢
      split
      · rename_i ho
        simp only [ho, ↓reduceIte, Bool.or_eq_true] at hv ⊢
        exact hv.imp (hot_finer hS hle) (hle.2.1 v)
      · rename_i ho
        simp only [ho, ↓reduceIte] at hv
        exact hle.2.1 v hv
    · simp only [turnT, agentT, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.any_eq_true] at ha ⊢
      rcases ha with ha | ⟨rfl, hc | ⟨o, ho, hi⟩⟩
      · exact Or.inl (hle.2.2 a ha)
      · exact Or.inr ⟨rfl, Or.inl hc⟩
      · exact Or.inr ⟨rfl, Or.inr ⟨o, ho, inT_finer hS hle hi⟩⟩
  | sys =>
    refine ⟨fun b hb => ?_, hle.2.1, hle.2.2⟩
    simp only [turnT, sysT, Bool.or_eq_true] at hb ⊢
    exact hb.imp (hle.1 b) id

/-- Monotonicity. A finer summary, from a smaller taint state, ends with a smaller one. -/
theorem taintAfter_finer {S' : Summary Agent Board Var} (hS : S'.Finer S) :
    ∀ (ts : List (Turn Agent)) {T T' : Taint Agent Board Var} (n : Nat), T'.Le T →
      (taintAfter cfg A U S' ts T' n).Le (taintAfter cfg A U S ts T n)
  | [], _, _, _, h => h
  | t :: ts, _, _, n, h => taintAfter_finer hS ts (n + 1) (turnT_finer hS n t h)

theorem reachSum_finer {S' : Summary Agent Board Var} (hS : S'.Finer S)
    (sched : List (Turn Agent)) {a : Agent} (h : reachSum cfg A U S' sched a = true) :
    reachSum cfg A U S sched a = true :=
  (taintAfter_finer hS sched 0 (Taint.Le.refl _)).2.2 a h

end

end Ir
