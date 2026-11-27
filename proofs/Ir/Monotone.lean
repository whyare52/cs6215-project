import Ir.Basic

/-!
# Hardening is monotone

Removing board readers or writers, visible variables, echoed variables, controlled agents or
injectable boards can only shrink the set of reachable agents.
-/

namespace Ir

variable {Agent Board Var Val Msg : Type}

/-- `cfg'` declares no more flow than `cfg`. Ownership is unchanged. -/
structure Weaker (cfg' cfg : Config Agent Board Var Val Msg) : Prop where
  owner : cfg'.owner = cfg.owner
  reader : ∀ b a, cfg'.reader b a = true → cfg.reader b a = true
  writer : ∀ b a, cfg'.writer b a = true → cfg.writer b a = true
  sees : ∀ a v, cfg'.sees a v = true → cfg.sees a v = true
  echoSees : ∀ v, cfg'.echoSees v = true → cfg.echoSees v = true

structure AdvWeaker (A' A : Adversary Agent Board) : Prop where
  controls : ∀ a, A'.controls a = true → A.controls a = true
  injects : ∀ b, A'.injects b = true → A.injects b = true

theorem Reach.mono {cfg' cfg : Config Agent Board Var Val Msg} {A' A : Adversary Agent Board}
    (hc : Weaker cfg' cfg) (hA : AdvWeaker A' A) {x : Agent} (h : Reach cfg' A' x) :
    Reach cfg A x := by
  induction h with
  | ctrl h => exact .ctrl (hA.controls _ h)
  | inj hi hm => exact .inj (hA.injects _ hi) (hc.reader _ _ hm)
  | board _ hmx hmy ih => exact .board ih (hc.writer _ _ hmx) (hc.reader _ _ hmy)
  | sees _ hs ih =>
    rw [hc.owner] at ih
    exact .sees ih (hc.sees _ _ hs)
  | echo _ he hmw hmy ih =>
    rw [hc.owner] at ih hmw
    exact .echo ih (hc.echoSees _ he) (hc.writer _ _ (by rw [hc.owner] at *; exact hmw))
      (hc.reader _ _ hmy)

/-- Terrarium's `create_channel` only invites agents that already share a board with the creator.
Each board of `cfg'` is either a board of `cfg`, with no new readers or writers, or such a
channel around a hub. Every writer of a channel can already write to the hub, and the hub can
already write to every reader. When readers and writers coincide, as in Terrarium, both say
the agent shares a board with the hub. -/
def ChannelsOf (cfg' cfg : Config Agent Board Var Val Msg) (A : Adversary Agent Board) : Prop :=
  cfg'.owner = cfg.owner ∧ cfg'.sees = cfg.sees ∧ cfg'.echoSees = cfg.echoSees ∧
  (∀ b, ((∀ a, cfg'.reader b a = true → cfg.reader b a = true) ∧
      (∀ a, cfg'.writer b a = true → cfg.writer b a = true)) ∨
    ∃ h, (∀ a, cfg'.writer b a = true → ∃ b₀, cfg.writer b₀ a = true ∧ cfg.reader b₀ h = true) ∧
      ∀ a, cfg'.reader b a = true → ∃ b₁, cfg.writer b₁ h = true ∧ cfg.reader b₁ a = true) ∧
  (∀ b, A.injects b = true → ∀ a, cfg'.reader b a = true → cfg.reader b a = true)

/-- Dynamic channels add no reachability, so the static analysis may ignore them. -/
theorem Reach.channels {cfg' cfg : Config Agent Board Var Val Msg} {A : Adversary Agent Board}
    (hc : ChannelsOf cfg' cfg A) {x : Agent} (h : Reach cfg' A x) : Reach cfg A x := by
  obtain ⟨ho, hs, he, hb, hi⟩ := hc
  induction h with
  | ctrl h => exact .ctrl h
  | inj hinj hm => exact .inj hinj (hi _ hinj _ hm)
  | @board b x y _ hmx hmy ih =>
    rcases hb b with ⟨hr, hw⟩ | ⟨hub, hwr, hrd⟩
    · exact .board ih (hw _ hmx) (hr _ hmy)
    · obtain ⟨b₀, hx₀, h₀⟩ := hwr x hmx
      obtain ⟨b₁, h₁, hy₁⟩ := hrd y hmy
      exact .board (.board ih hx₀ h₀) h₁ hy₁
  | sees _ hsv ih =>
    rw [ho] at ih
    exact .sees ih (by rw [← hs]; exact hsv)
  | @echo v w b y _ hev hmw hmy ih =>
    rw [ho] at ih hmw
    have hev' : cfg.echoSees v = true := by rw [← he]; exact hev
    rcases hb b with ⟨hr, hw⟩ | ⟨hub, hwr, hrd⟩
    · exact .echo (w := w) ih hev' (hw _ hmw) (hr _ hmy)
    · have hmw' : cfg'.writer b (cfg'.owner w) = true := by rw [ho]; exact hmw
      obtain ⟨b₀, hw₀, h₀⟩ := hwr _ hmw'
      obtain ⟨b₁, h₁, hy₁⟩ := hrd y hmy
      rw [ho] at hw₀
      exact .board (.echo (w := w) ih hev' hw₀ h₀) h₁ hy₁

end Ir
