import Ir.Monotone
import Ir.Check

/-!
# A clear does not change `Reach`

kaymen99's email graph handles customer A's email, then customer B's, in one run. The writer
keeps its drafts in `writer_messages`. The bug clears that list in a routing function, which
acts on a throwaway copy, so B's writer reads A's drafts. The fix adds a node that returns
`RemoveMessage` and empties the list between customers.

With readers, writers and `replace`, the fix is expressible, but `Reach` cannot tell it from the
bug. A config says who may write a board, not who must clear it, so the fix's config only
adds the reset node as a writer. `Reach` is monotone in writers (`Reach.mono`), so the fix
reaches at least the agents the bug does. Telling them apart needs the schedule and the
behaviour, since the clear helps only because it runs between A's turns and B's.

The writer is split per customer (`writeA`, `writeB`), as the second model gap asks. Without
the split one writer node serves both customers and is reached in both configs by A's email
directly.
-/

namespace Ir.ClearGap

inductive Agent where
  | writeA | writeB | reset
  deriving DecidableEq, Repr

inductive Board where
  | emailA | emailB | writerMessages
  deriving DecidableEq, Repr

open Agent Board

/-- Each customer's writer reads its email, and both read and write the shared drafts. -/
def bug : Config Agent Board Empty Nat String where
  reader
    | emailA, a => a == writeA
    | emailB, a => a == writeB
    | writerMessages, a => a == writeA || a == writeB
  writer
    | writerMessages, a => a == writeA || a == writeB
    | _, _ => false
  owner v := nomatch v
  sees _ v := nomatch v
  echoSees v := nomatch v
  echo _ := ""

/-- The fix adds the reset node as a writer of the drafts, where it clears them. -/
def fix : Config Agent Board Empty Nat String :=
  { bug with writer := fun b a => bug.writer b a || (b == writerMessages && a == reset) }

/-- Customer A is the attacker, through the email it sends. -/
def customerA : Adversary Agent Board where
  controls _ := false
  injects b := b == emailA

def world : Universe Agent Board Empty where
  agents := [writeA, writeB, reset]
  boards := [emailA, emailB, writerMessages]
  vars := []
  hA a := by cases a <;> simp
  hB b := by cases b <;> simp
  hV := fun v => nomatch v

/-- The bug's config declares no more flow than the fix's. -/
theorem bug_weaker : Weaker bug fix :=
  ⟨rfl, fun _ _ h => h, fun _ _ h => by simp [fix, h], fun _ _ h => h, fun _ h => h⟩

/-- A's drafts reach B's writer in the bug. -/
theorem bug_reaches_writeB : Reach bug customerA writeB :=
  Reach.board (b := writerMessages) (x := writeA) (Reach.inj (b := emailA) rfl rfl) rfl rfl

/-- So they do in the fix too. No config-level account of the clear can separate the two. -/
theorem fix_reaches_writeB : Reach fix customerA writeB :=
  Reach.mono bug_weaker ⟨fun _ h => h, fun _ h => h⟩ bug_reaches_writeB

/-- Both configs reach the same agents. -/
example : reachable bug customerA world = reachable fix customerA world := by decide

end Ir.ClearGap
