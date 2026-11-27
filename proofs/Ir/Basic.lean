/-!
# Protocol IR for multi-agent testbeds

Syntax and trace semantics of a Terrarium-style testbed, as a transition system.
Agents share boards, own variables, and commit with `attend`. A board has readers, who see
it, and writers, who may append to it or replace its contents, as a LangGraph state key or
store namespace has nodes that read it and nodes that write it.
The environment shows each agent the variables it `sees`, and echoes every commit
(with a summary of the assignment, like `joint_reward`) to the boards the committer writes.
-/

namespace Ir

/-- Static declarations. Terrarium itself sets `sees` and `echoSees` to true everywhere.
`echo` summarises the variables in `echoSees` after each commit.
`writer` defaults to `reader`, so a config that gives only `reader` means every agent on a
board both reads and writes it, as Terrarium's boards do. -/
structure Config (Agent Board Var Val Msg : Type) where
  reader : Board → Agent → Bool
  writer : Board → Agent → Bool := reader
  owner : Var → Agent
  sees : Agent → Var → Bool
  echoSees : Var → Bool
  echo : (Var → Option Val) → Msg

/-- The same config with board `b` read and written by exactly the agents in `m b`. -/
def Config.withMembers {Agent Board Var Val Msg : Type} (cfg : Config Agent Board Var Val Msg)
    (m : Board → Agent → Bool) : Config Agent Board Var Val Msg :=
  { cfg with reader := m, writer := m }

/-- What the adversary holds. Agents it drives and boards it posts to as SYS. -/
structure Adversary (Agent Board : Type) where
  controls : Agent → Bool
  injects : Board → Bool

/-- `replace b m` sets board `b` to the single entry `m`, or empties it when `m` is `none`,
like LangGraph's `RemoveMessage` or an overwriting reducer. A longer replacement is a
`replace` followed by posts in the same turn, so one action adds at most one entry. -/
inductive Action (Board Var Val Msg : Type) where
  | post (b : Board) (m : Msg)
  | replace (b : Board) (m : Option Msg)
  | attend (v : Var) (t : Val)
  | skip

inductive Turn (Agent : Type) where
  | agent (a : Agent)
  | sys
  deriving DecidableEq

/-- Clearing a board is replacing its contents with nothing. -/
abbrev Action.clear {Board Var Val Msg : Type} (b : Board) : Action Board Var Val Msg :=
  .replace b none

/-- Board logs, with `none` as the SYS sender, and the joint assignment. -/
structure State (Agent Board Var Val Msg : Type) where
  logs : Board → List (Option Agent × Msg)
  assign : Var → Option Val

/-- Honest agents act on the turn index (standing in for a fixed random tape) and their view.
A turn is a list of actions, all chosen from the one view, as a graph node returns several
writes at once. -/
abbrev Behaviour (Agent Board Var Val Msg : Type) :=
  Agent → Nat → State Agent Board Var Val Msg → List (Action Board Var Val Msg)

/-- The adversary sees the full state. -/
structure Attack (Agent Board Var Val Msg : Type) where
  act : Agent → Nat → State Agent Board Var Val Msg → List (Action Board Var Val Msg)
  inject : Nat → State Agent Board Var Val Msg → Option (Board × Msg)

section

variable {Agent Board Var Val Msg : Type}
  [DecidableEq Agent] [DecidableEq Board] [DecidableEq Var]
  (cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board)
  (honest : Behaviour Agent Board Var Val Msg) (adv : Attack Agent Board Var Val Msg)

/-- Agent `a` sees the variables it may see and the boards it reads. -/
def view (a : Agent) (s : State Agent Board Var Val Msg) : State Agent Board Var Val Msg where
  logs b := if cfg.reader b a then s.logs b else []
  assign v := if cfg.sees a v then s.assign v else none

def post (b : Board) (e : Option Agent × Msg)
    (s : State Agent Board Var Val Msg) : State Agent Board Var Val Msg :=
  { s with logs := fun b' => if b' = b then s.logs b ++ [e] else s.logs b' }

/-- Set board `b` to the log `l`, dropping what it held. -/
def setLog (b : Board) (l : List (Option Agent × Msg))
    (s : State Agent Board Var Val Msg) : State Agent Board Var Val Msg :=
  { s with logs := fun b' => if b' = b then l else s.logs b' }

omit [DecidableEq Agent] [DecidableEq Var] in
theorem post_eq_setLog (b : Board) (e : Option Agent × Msg)
    (s : State Agent Board Var Val Msg) : post b e s = setLog b (s.logs b ++ [e]) s := rfl

/-- Write `v := t`, then echo the new assignment to every board `x` writes. -/
def commit (x : Agent) (v : Var) (t : Val)
    (s : State Agent Board Var Val Msg) : State Agent Board Var Val Msg :=
  let a' := fun v' => if v' = v then some t else s.assign v'
  { logs := fun b =>
      if cfg.writer b x then
        s.logs b ++ [(none, cfg.echo (fun v' => if cfg.echoSees v' then a' v' else none))]
      else s.logs b
    assign := a' }

/-- Posting and replacing need write access. `attend` needs ownership and is write-once. -/
def perform (x : Agent) :
    Action Board Var Val Msg → State Agent Board Var Val Msg →
    State Agent Board Var Val Msg
  | .post b m, s => if cfg.writer b x then post b (some x, m) s else s
  | .replace b m, s => if cfg.writer b x then setLog b (m.toList.map (some x, ·)) s else s
  | .attend v t, s =>
    if cfg.owner v = x ∧ s.assign v = none then commit cfg x v t s else s
  | .skip, s => s

/-- A turn performs its actions in order, each on the state the previous one left. -/
def performAll (x : Agent) :
    List (Action Board Var Val Msg) → State Agent Board Var Val Msg →
    State Agent Board Var Val Msg
  | [], s => s
  | act :: acts, s => performAll x acts (perform cfg x act s)

def choose (n : Nat) (x : Agent) (s : State Agent Board Var Val Msg) :
    List (Action Board Var Val Msg) :=
  if A.controls x then adv.act x n s else honest x n (view cfg x s)

/-- SYS injection only appends. It models text an outside source plants, such as a tool
result or an email, which cannot erase the board. A controlled writer can still replace. -/
def sysStep (n : Nat) (s : State Agent Board Var Val Msg) : State Agent Board Var Val Msg :=
  match adv.inject n s with
  | some (b, m) => if A.injects b then post b (none, m) s else s
  | none => s

def step (n : Nat) :
    Turn Agent → State Agent Board Var Val Msg → State Agent Board Var Val Msg
  | .agent x, s => performAll cfg x (choose cfg A honest adv n x s) s
  | .sys, s => sysStep A adv n s

/-- Run a schedule. The turn index `n` starts at 0 unless given. -/
def run :
    List (Turn Agent) → State Agent Board Var Val Msg → optParam Nat 0 →
    State Agent Board Var Val Msg
  | [], s, _ => s
  | t :: ts, s, n => run ts (step cfg A honest adv n t s) (n + 1)

/-- The actions agent `a` takes along a run, one list per turn, in order. -/
def actionsOf (a : Agent) :
    List (Turn Agent) → State Agent Board Var Val Msg → optParam Nat 0 →
    List (List (Action Board Var Val Msg))
  | [], _, _ => []
  | t :: ts, s, n =>
    (match t with
      | .agent x => if x = a then [choose cfg A honest adv n a s] else []
      | .sys => []) ++
    actionsOf a ts (step cfg A honest adv n t s) (n + 1)

/-- Static flow from the adversary. It is flow-insensitive, so a `replace` that erases a
board counts as a write like a post, and never cuts an edge.
- `inj`: SYS posts reach every reader of an injectable board.
- `board`: a writer's posts and replacements reach every reader.
- `sees`: a reachable owner's commit reaches whoever sees the variable.
- `echo`: if the echo summarises the variable, it reaches the readers of every board an
  owner writes. -/
inductive Reach : Agent → Prop
  | ctrl {x} : A.controls x = true → Reach x
  | inj {b x} : A.injects b = true → cfg.reader b x = true → Reach x
  | board {b x y} : Reach x → cfg.writer b x = true → cfg.reader b y = true → Reach y
  | sees {v y} : Reach (cfg.owner v) → cfg.sees y v = true → Reach y
  | echo {v w b y} : Reach (cfg.owner v) → cfg.echoSees v = true →
      cfg.writer b (cfg.owner w) = true →
      cfg.reader b y = true → Reach y

end

end Ir
