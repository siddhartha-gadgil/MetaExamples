import Lean

open Lean Meta

example : 2 ≤ 6 := by
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_step
  apply Nat.le_refl

example : 2 ≤ 6 := by
  repeat (first | apply Nat.le_refl | apply Nat.le_step)

macro "nat_le" : tactic =>
  `(tactic| repeat (first | apply Nat.le_refl | apply Nat.le_step))

example : 10 ≤ 20 := by
  nat_le

macro "repeat_apply" t₁:term "then" t₂:term :tactic => do
  `(tactic| repeat (first | apply $t₂ | apply $t₁))

example : 10 ≤ 15 := by
  repeat_apply Nat.le_step then Nat.le_refl

example : 12 ≤ 26 := by
  repeat_apply Nat.succ_le_succ then Nat.zero_le
