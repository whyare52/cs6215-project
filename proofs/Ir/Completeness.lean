import Ir.Confidentiality

/-!
# Completeness

Every reachable agent can be influenced. For each reachable honest agent `a` there are an honest
behaviour, a schedule and two adversary attacks under which `a` sees different views.
So `Reach` is exact for worst-case behaviours, and every warning is a real attack.

The witness is a relay behaviour. An agent whose view is nonempty tries every post and commit
it can, the loud adversary does the same and injects into every board, and the quiet adversary
does nothing. In the quiet run the state stays empty, while in the loud run every reachable
agent's view nonempty within becomes a bounded number of rounds.

The relay only posts and commits, never replaces, so it realises every `board` edge with a
post from a writer to the readers. Without a clear, boards only grow along its runs.

The echo edge needs an informative echo, so we assume each echoed variable is seen by everyone,
as in Terrarium. Without that assumption the echo edge can be a false alarm.
-/

set_option linter.unusedSectionVars false

namespace Ir.Completeness

open Ir

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]

/-- A testbed with finite universes and one message and slot to send. -/
structure Setup (Agent Board Var Val Msg : Type) where
  cfg : Config Agent Board Var Val Msg
  A : Adversary Agent Board
  agents : List Agent
  boards : List Board
  vars : List Var
  m : Msg
  t : Val

variable (W : Setup Agent Board Var Val Msg)

def cand : List (Action Board Var Val Msg) :=
  W.vars.map (fun v => .attend v W.t) ++ W.boards.map (fun b => .post b W.m)

def pick (n : Nat) : Action Board Var Val Msg :=
  (cand W).getD (n % (cand W).length) .skip

def tainted (s : State Agent Board Var Val Msg) : Bool :=
  W.boards.any (fun b => !(s.logs b).isEmpty) || W.vars.any (fun v => (s.assign v).isSome)

def relay : Behaviour Agent Board Var Val Msg :=
  fun _ n s => if tainted W s then [pick W n] else []

def loud : Attack Agent Board Var Val Msg :=
  ⟨fun _ n _ => [pick W n], fun n _ => (W.boards[n % W.boards.length]?).map fun b => (b, W.m)⟩

def quiet : Attack Agent Board Var Val Msg := ⟨fun _ _ _ => [], fun _ _ => none⟩

def empty : State Agent Board Var Val Msg := ⟨fun _ => [], fun _ => none⟩

def block (x : Agent) : List (Turn Agent) := List.replicate ((cand W).length + 1) (.agent x)

def sysBlock : List (Turn Agent) := List.replicate (W.boards.length + 1) .sys

def round : List (Turn Agent) := W.agents.flatMap (block W) ++ sysBlock W

def rounds : Nat → List (Turn Agent)
  | 0 => []
  | k + 1 => rounds k ++ round W

/-! ## Growth. Without clears, logs only grow, and commits are write-once. -/

/-- The action does not clear a board. A replace with an entry leaves the board nonempty. -/
def keeps : Action Board Var Val Msg → Bool
  | .replace _ none => false
  | _ => true

/-- No agent's turn clears a board. -/
def NoClear (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg) : Prop :=
  ∀ n x s, ∀ act ∈ choose cfg A honest adv n x s, keeps act = true

def Grows (s s' : State Agent Board Var Val Msg) : Prop :=
  (∀ b, s.logs b ≠ [] → s'.logs b ≠ []) ∧ (∀ v, s.assign v ≠ none → s'.assign v ≠ none)

theorem Grows.refl (s : State Agent Board Var Val Msg) : Grows s s :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem Grows.trans {s₁ s₂ s₃ : State Agent Board Var Val Msg}
    (h₁ : Grows s₁ s₂) (h₂ : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨fun b h => h₂.1 b (h₁.1 b h), fun v h => h₂.2 v (h₁.2 v h)⟩

theorem grows_post (b : Board) (e : Option Agent × Msg) (s : State Agent Board Var Val Msg) :
    Grows s (post b e s) := by
  refine ⟨fun b' h => ?_, fun _ h => h⟩
  simp only [post]
  split <;> simp_all

theorem post_logs_ne (b : Board) (e : Option Agent × Msg) (s : State Agent Board Var Val Msg) :
    (post b e s).logs b ≠ [] := by
  simp [post]

theorem grows_commit (cfg : Config Agent Board Var Val Msg) (x : Agent) (v : Var) (t : Val)
    (s : State Agent Board Var Val Msg) : Grows s (commit cfg x v t s) := by
  refine ⟨fun b h => ?_, fun v' h => ?_⟩
  · simp only [commit]
    split <;> simp_all
  · simp only [commit]
    split <;> simp_all

theorem grows_perform (cfg : Config Agent Board Var Val Msg) (x : Agent)
    (act : Action Board Var Val Msg) (s : State Agent Board Var Val Msg)
    (hk : keeps act = true) : Grows s (perform cfg x act s) := by
  cases act with
  | post b m =>
    simp only [perform]; split
    · exact grows_post _ _ _
    · exact Grows.refl _
  | replace b m =>
    cases m with
    | none => simp [keeps] at hk
    | some m =>
      simp only [perform]; split
      · refine ⟨fun b' h => ?_, fun _ h => h⟩
        simp only [setLog]
        split <;> simp_all
      · exact Grows.refl _
  | attend v t =>
    simp only [perform]; split
    · exact grows_commit _ _ _ _ _
    · exact Grows.refl _
  | skip => exact Grows.refl _

theorem grows_performAll (cfg : Config Agent Board Var Val Msg) (x : Agent) :
    ∀ (acts : List (Action Board Var Val Msg)) (s : State Agent Board Var Val Msg),
      (∀ act ∈ acts, keeps act = true) → Grows s (performAll cfg x acts s)
  | [], _, _ => Grows.refl _
  | act :: acts, s, hk =>
    (grows_perform cfg x act s (hk act (by simp))).trans
      (grows_performAll cfg x acts _ fun a ha => hk a (by simp [ha]))

theorem grows_step (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (hk : NoClear cfg A honest adv) (n : Nat) (t : Turn Agent)
    (s : State Agent Board Var Val Msg) :
    Grows s (step cfg A honest adv n t s) := by
  cases t with
  | agent x => exact grows_performAll _ _ _ _ (hk n x s)
  | sys =>
    simp only [step, sysStep]
    split
    · split
      · exact grows_post _ _ _
      · exact Grows.refl _
    · exact Grows.refl _

theorem grows_run (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (hk : NoClear cfg A honest adv) (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg}, Grows s (run cfg A honest adv sched s n) := by
  induction sched with
  | nil => intros; exact Grows.refl _
  | cons t ts ih => intro n s; exact (grows_step cfg A honest adv hk n t s).trans ih

theorem run_append (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (l₁ l₂ : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      run cfg A honest adv (l₁ ++ l₂) s n =
        run cfg A honest adv l₂ (run cfg A honest adv l₁ s n) (n + l₁.length) := by
  induction l₁ with
  | nil => intros; simp [run]
  | cons t ts ih =>
    intro n s
    simp only [List.cons_append, run, List.length_cons]
    rw [ih]
    congr 1
    omega

theorem viewsOf_append (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (a : Agent) (l₁ l₂ : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      viewsOf cfg A honest adv a (l₁ ++ l₂) s n =
        viewsOf cfg A honest adv a l₁ s n ++
          viewsOf cfg A honest adv a l₂ (run cfg A honest adv l₁ s n) (n + l₁.length) := by
  induction l₁ with
  | nil => intros; simp [viewsOf, run]
  | cons t ts ih =>
    intro n s
    simp only [List.cons_append, viewsOf, run, List.length_cons, List.append_assoc]
    rw [ih]
    congr 3
    omega

/-! ## Taint -/

theorem tainted_view_iff (x : Agent) (s : State Agent Board Var Val Msg) :
    tainted W (view W.cfg x s) = true ↔
      (∃ b ∈ W.boards, W.cfg.reader b x = true ∧ s.logs b ≠ []) ∨
        (∃ v ∈ W.vars, W.cfg.sees x v = true ∧ s.assign v ≠ none) := by
  simp only [tainted, view, Bool.or_eq_true, List.any_eq_true]
  apply or_congr
  · apply exists_congr; intro b; apply and_congr_right; intro _
    cases W.cfg.reader b x <;> simp
  · apply exists_congr; intro v; apply and_congr_right; intro _
    cases W.cfg.sees x v <;> simp [Option.isSome_iff_ne_none]

theorem tainted_mono {x : Agent} {s s' : State Agent Board Var Val Msg}
    (h : tainted W (view W.cfg x s) = true) (hg : Grows s s') :
    tainted W (view W.cfg x s') = true := by
  rw [tainted_view_iff] at h ⊢
  rcases h with ⟨b, hb, hm, hl⟩ | ⟨v, hv, hs, ha⟩
  · exact .inl ⟨b, hb, hm, hg.1 b hl⟩
  · exact .inr ⟨v, hv, hs, hg.2 v ha⟩

theorem not_tainted_empty (x : Agent) : tainted W (view W.cfg x empty) = false := by
  apply Bool.eq_false_iff.2
  intro h
  rw [tainted_view_iff] at h
  rcases h with ⟨_, _, _, hl⟩ | ⟨_, _, _, ha⟩
  · exact hl rfl
  · exact ha rfl

/-- Active agents act loudly. -/
def Active (x : Agent) (s : State Agent Board Var Val Msg) : Prop :=
  W.A.controls x = true ∨ tainted W (view W.cfg x s) = true

theorem Active.mono {x : Agent} {s s' : State Agent Board Var Val Msg}
    (h : Active W x s) (hg : Grows s s') : Active W x s' :=
  Or.imp id (fun h => tainted_mono W h hg) h

theorem choose_active {n : Nat} {x : Agent} {s : State Agent Board Var Val Msg}
    (h : Active W x s) : choose W.cfg W.A (relay W) (loud W) n x s = [pick W n] := by
  unfold choose
  split
  · rfl
  · rename_i hc
    have ht : tainted W (view W.cfg x s) = true := by
      rcases h with h | h
      · exact absurd h hc
      · exact h
    simp [relay, ht]

theorem keeps_pick (n : Nat) : keeps (pick W n) = true := by
  unfold pick
  rw [List.getD_eq_getElem?_getD]
  cases h : (cand W)[n % (cand W).length]? with
  | none => rfl
  | some a =>
    have := List.mem_of_getElem? h
    simp only [cand, List.mem_append, List.mem_map] at this
    rcases this with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-- The loud run never clears a board. -/
theorem loud_noClear : NoClear W.cfg W.A (relay W) (loud W) := by
  intro n x s act h
  simp only [choose, relay, loud] at h
  split at h
  · simp only [List.mem_singleton] at h; subst h; exact keeps_pick W n
  · split at h
    · simp only [List.mem_singleton] at h; subst h; exact keeps_pick W n
    · simp at h

/-! ## Covering every candidate within a block -/

theorem mod_cover {K : Nat} (hK : 0 < K) (n₀ i : Nat) (hi : i < K) :
    ∃ j < K, (n₀ + j) % K = i := by
  refine ⟨(i + (K - n₀ % K)) % K, Nat.mod_lt _ hK, ?_⟩
  have hr := Nat.mod_lt n₀ hK
  rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod_mod]
  have : n₀ % K + (i + (K - n₀ % K)) = i + K := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

theorem pick_cover {c : Action Board Var Val Msg} (hc : c ∈ cand W) (n₀ : Nat) :
    ∃ j < (cand W).length, pick W (n₀ + j) = c := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hK : 0 < (cand W).length := by omega
  obtain ⟨j, hj, hji⟩ := mod_cover hK n₀ i hi
  refine ⟨j, hj, ?_⟩
  simp only [pick, hji]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem replicate_split {α : Type} (a : α) {j K : Nat} (hj : j < K + 1) :
    List.replicate (K + 1) a = List.replicate j a ++ a :: List.replicate (K - j) a := by
  have : K + 1 = j + (K - j + 1) := by omega
  rw [this, ← List.replicate_append_replicate, List.replicate_succ]

abbrev R (adv : Attack Agent Board Var Val Msg) (sched : List (Turn Agent))
    (s : State Agent Board Var Val Msg) (n : Nat := 0) : State Agent Board Var Val Msg :=
  run W.cfg W.A (relay W) adv sched s n

/-- In its block, an active agent performs every candidate. -/
theorem block_effect {x : Agent} {s : State Agent Board Var Val Msg} (hx : Active W x s)
    (n₀ : Nat) {c : Action Board Var Val Msg} (hc : c ∈ cand W) :
    ∃ s₁, Grows (perform W.cfg x c s₁) (R W (loud W) (block W x) s n₀) := by
  obtain ⟨j, hj, hpick⟩ := pick_cover W hc n₀
  have hsplit := replicate_split (Turn.agent x) (K := (cand W).length) (by omega : j < _ + 1)
  let s₁ := R W (loud W) (List.replicate j (.agent x)) s n₀
  have hs₁ : Active W x s₁ := Active.mono W hx (grows_run _ _ _ _ (loud_noClear W) _)
  refine ⟨s₁, ?_⟩
  simp only [R, block, hsplit, run_append, List.length_replicate, run, step]
  rw [choose_active W hs₁, hpick]
  exact grows_run _ _ _ _ (loud_noClear W) _

theorem sys_effect {b : Board} (hb : b ∈ W.boards) (hi : W.A.injects b = true)
    (n₀ : Nat) (s : State Agent Board Var Val Msg) :
    (R W (loud W) (sysBlock W) s n₀).logs b ≠ [] := by
  obtain ⟨i, hiB, rfl⟩ := List.getElem_of_mem hb
  have hB : 0 < W.boards.length := by omega
  obtain ⟨j, hj, hji⟩ := mod_cover hB n₀ i hiB
  have hsplit := replicate_split (Turn.sys : Turn Agent) (K := W.boards.length)
    (by omega : j < _ + 1)
  simp only [R, sysBlock, hsplit, run_append, List.length_replicate, run, step]
  refine (grows_run _ _ _ _ (loud_noClear W) _).1 _ ?_
  simp only [sysStep, loud, hji, List.getElem?_eq_getElem hiB, Option.map_some, hi, ite_true]
  exact post_logs_ne _ _ _

/-! ## Rounds -/

theorem segment {adv : Attack Agent Board Var Val Msg} {sched pre mid post : List (Turn Agent)}
    (h : sched = pre ++ mid ++ post) (hk : NoClear W.cfg W.A (relay W) adv) (n : Nat)
    (s : State Agent Board Var Val Msg) :
    Grows (R W adv mid (R W adv pre s n) (n + pre.length)) (R W adv sched s n) := by
  subst h
  simp only [R]
  rw [run_append, run_append]
  exact grows_run _ _ _ _ hk _

theorem round_split {x : Agent} (hx : x ∈ W.agents) :
    ∃ pre post, round W = pre ++ block W x ++ post := by
  obtain ⟨l₁, l₂, h⟩ := List.append_of_mem hx
  refine ⟨l₁.flatMap (block W), l₂.flatMap (block W) ++ sysBlock W, ?_⟩
  simp [round, h, List.flatMap_append, List.append_assoc]

/-- An active agent posts to each board it writes and commits each of its variables. -/
theorem round_effect {x : Agent} (hx : x ∈ W.agents) {s : State Agent Board Var Val Msg}
    (hact : Active W x s) (n : Nat) :
    (∀ b ∈ W.boards, W.cfg.writer b x = true → (R W (loud W) (round W) s n).logs b ≠ []) ∧
    (∀ v ∈ W.vars, W.cfg.owner v = x → (R W (loud W) (round W) s n).assign v ≠ none) := by
  obtain ⟨pre, post, hr⟩ := round_split W hx
  have hseg := segment W (adv := loud W) hr (loud_noClear W) n s
  have hact' : Active W x (R W (loud W) pre s n) :=
    Active.mono W hact (grows_run _ _ _ _ (loud_noClear W) _)
  constructor
  · intro b hb hm
    obtain ⟨s₁, hg⟩ := block_effect W hact' (n + pre.length)
      (c := .post b W.m) (by simp [cand, hb])
    refine (hg.trans hseg).1 b ?_
    simp only [perform, hm, ite_true]
    exact post_logs_ne _ _ _
  · intro v hv ho
    obtain ⟨s₁, hg⟩ := block_effect W hact' (n + pre.length)
      (c := .attend v W.t) (by simp [cand, hv])
    refine (hg.trans hseg).2 v ?_
    simp only [perform, ho, true_and]
    split
    · simp [commit]
    · rename_i hn; exact hn

theorem round_sys {b : Board} (hb : b ∈ W.boards) (hi : W.A.injects b = true) (n : Nat)
    (s : State Agent Board Var Val Msg) : (R W (loud W) (round W) s n).logs b ≠ [] := by
  have hseg := segment W (adv := loud W) (sched := round W) (pre := W.agents.flatMap (block W))
    (mid := sysBlock W) (post := []) (by simp [round]) (loud_noClear W) n s
  exact hseg.1 b (sys_effect W hb hi _ _)

/-- State after `k` loud rounds. -/
def S (k : Nat) : State Agent Board Var Val Msg := R W (loud W) (rounds W k) empty

theorem S_succ (k : Nat) :
    S W (k + 1) = R W (loud W) (round W) (S W k) (rounds W k).length := by
  simp only [S, rounds, R, run_append, Nat.zero_add]

theorem S_grows {k k' : Nat} (h : k ≤ k') : Grows (S W k) (S W k') := by
  induction h with
  | refl => exact Grows.refl _
  | step _ ih => rw [S_succ]; exact ih.trans (grows_run _ _ _ _ (loud_noClear W) _)

/-- Every reachable agent becomes active after finitely many loud rounds. -/
theorem reach_active (hA : ∀ a, a ∈ W.agents) (hB : ∀ b, b ∈ W.boards) (hV : ∀ v, v ∈ W.vars)
    (hecho : ∀ v, W.cfg.echoSees v = true → ∀ y, W.cfg.sees y v = true)
    {x : Agent} (hr : Reach W.cfg W.A x) : ∃ k, Active W x (S W k) := by
  induction hr with
  | ctrl h => exact ⟨0, .inl h⟩
  | @inj b x hi hm =>
    refine ⟨1, .inr ?_⟩
    rw [tainted_view_iff, S_succ]
    exact .inl ⟨b, hB b, hm, round_sys W (hB b) hi _ _⟩
  | @board b x y _ hmx hmy ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, .inr ?_⟩
    rw [tainted_view_iff, S_succ]
    exact .inl ⟨b, hB b, hmy, (round_effect W (hA x) hk _).1 b (hB b) hmx⟩
  | @sees v y _ hs ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, .inr ?_⟩
    rw [tainted_view_iff, S_succ]
    exact .inr ⟨v, hV v, hs, (round_effect W (hA _) hk _).2 v (hV v) rfl⟩
  | @echo v w b y _ he _ _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, .inr ?_⟩
    rw [tainted_view_iff, S_succ]
    exact .inr ⟨v, hV v, hecho v he y, (round_effect W (hA _) hk _).2 v (hV v) rfl⟩

/-! ## The quiet run stays empty -/

theorem quiet_step (n : Nat) (t : Turn Agent) :
    step W.cfg W.A (relay W) quiet n t empty = empty := by
  cases t with
  | agent x =>
    simp only [step, choose]
    split
    · rfl
    · simp [relay, not_tainted_empty, performAll]
  | sys => rfl

theorem quiet_views (a : Agent) (sched : List (Turn Agent)) :
    ∀ {n : Nat}, ∀ e ∈ viewsOf W.cfg W.A (relay W) quiet a sched empty n,
      e = view W.cfg a empty := by
  induction sched with
  | nil => intro _ e he; simp [viewsOf] at he
  | cons t ts ih =>
    intro n e he
    simp only [viewsOf, quiet_step, List.mem_append] at he
    rcases he with he | he
    · cases t with
      | agent x =>
        simp only at he
        split at he
        · simpa using he
        · simp at he
      | sys => simp at he
    · exact ih e he

theorem loud_views (a : Agent) (sched : List (Turn Agent)) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      ∀ e ∈ viewsOf W.cfg W.A (relay W) (loud W) a sched s n,
        ∃ s', Grows s s' ∧ e = view W.cfg a s' := by
  induction sched with
  | nil => intro _ _ e he; simp [viewsOf] at he
  | cons t ts ih =>
    intro n s e he
    simp only [viewsOf, List.mem_append] at he
    rcases he with he | he
    · cases t with
      | agent x =>
        simp only at he
        split at he
        · exact ⟨s, Grows.refl _, by simpa using he⟩
        · simp at he
      | sys => simp at he
    · obtain ⟨s', hg, rfl⟩ := ih e he
      exact ⟨s', (grows_step _ _ _ _ (loud_noClear W) _ _ _).trans hg, rfl⟩

theorem viewsOf_ne_nil (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
    (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)
    (a : Agent) (sched : List (Turn Agent)) (ha : Turn.agent a ∈ sched) :
    ∀ {n : Nat} {s : State Agent Board Var Val Msg},
      viewsOf cfg A honest adv a sched s n ≠ [] := by
  induction sched with
  | nil => simp at ha
  | cons t ts ih =>
    intro n s
    simp only [viewsOf]
    rcases List.mem_cons.1 ha with h | h
    · subst h; simp
    · intro hn
      exact ih h (List.append_eq_nil_iff.1 hn).2

/-- Completeness. Every reachable honest agent can be influenced by the adversary. -/
theorem completeness (hA : ∀ a, a ∈ W.agents) (hB : ∀ b, b ∈ W.boards) (hV : ∀ v, v ∈ W.vars)
    (hecho : ∀ v, W.cfg.echoSees v = true → ∀ y, W.cfg.sees y v = true)
    {a : Agent} (hc : W.A.controls a = false) (hr : Reach W.cfg W.A a) :
    ∃ sched, viewsOf W.cfg W.A (relay W) (loud W) a sched empty ≠
      viewsOf W.cfg W.A (relay W) quiet a sched empty := by
  obtain ⟨k, hk⟩ := reach_active W hA hB hV hecho hr
  have ht : tainted W (view W.cfg a (S W k)) = true := by
    rcases hk with h | h
    · rw [hc] at h; exact absurd h Bool.false_ne_true
    · exact h
  refine ⟨rounds W (k + 1), fun heq => ?_⟩
  have hmem : Turn.agent a ∈ round W := by
    obtain ⟨pre, post, hr⟩ := round_split W (hA a)
    rw [hr]; simp [block]
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _
    (viewsOf_ne_nil W.cfg W.A (relay W) (loud W) a (round W) hmem
      (n := (rounds W k).length) (s := S W k))
  obtain ⟨s', hg, rfl⟩ := loud_views W a _ e he
  have hin : view W.cfg a s' ∈
      viewsOf W.cfg W.A (relay W) (loud W) a (rounds W (k + 1)) empty := by
    simp only [rounds, viewsOf_append, Nat.zero_add]
    exact List.mem_append_right _ he
  rw [heq] at hin
  have := quiet_views W a _ _ hin
  have h1 := tainted_mono W ht hg
  rw [this, not_tainted_empty] at h1
  exact Bool.false_ne_true h1

/-- Exactness. Under an informative echo, an honest agent is reachable exactly when some honest
behaviour and pair of adversary attacks give it different views. -/
theorem reach_iff_influence (hA : ∀ a, a ∈ W.agents) (hB : ∀ b, b ∈ W.boards)
    (hV : ∀ v, v ∈ W.vars)
    (hecho : ∀ v, W.cfg.echoSees v = true → ∀ y, W.cfg.sees y v = true)
    {a : Agent} (hc : W.A.controls a = false) :
    Reach W.cfg W.A a ↔
      ∃ (honest : Behaviour Agent Board Var Val Msg) (adv₁ adv₂ : Attack Agent Board Var Val Msg)
        (sched : List (Turn Agent)) (s₀ : State Agent Board Var Val Msg),
        viewsOf W.cfg W.A honest adv₁ a sched s₀ ≠ viewsOf W.cfg W.A honest adv₂ a sched s₀ := by
  constructor
  · intro hr
    obtain ⟨sched, h⟩ := completeness W hA hB hV hecho hc hr
    exact ⟨relay W, loud W, quiet, sched, empty, h⟩
  · rintro ⟨honest, adv₁, adv₂, sched, s₀, h⟩
    exact Classical.byContradiction fun hr => h (viewsOf_eq hr sched (Agree.refl s₀))

end Ir.Completeness
