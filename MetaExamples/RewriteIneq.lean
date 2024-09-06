import Lean
import MetaExamples.Basic
open Lean Meta Elab Tactic

/-!
## Rewriting with Inequalities: `rw_le`

We now give a more substantial example. This can be done with just macros, but we will use metaprogramming to illustrate the principles.

The tactic `rw_le h` works if the goal is of the form `a ≤ b` and `h` is a proof of `c ≤ d`, with `a`, `b`, `c` and `d` all natural numbers. If `a = c` or `b = d` or both, then it rewrites the goal.

Our first step is to recognize when an expression (for example the goal) is of the correct form.
-/
#check Expr.eq? -- Expr → Option (Expr × Expr × Expr)
#check Expr.app2? -- Expr → Name → Option (Expr × Expr)

#check Nat.le -- Nat → Nat → Prop
#expr [(1: Nat) ≤ 2]

def matchLe (e: Expr) :
    MetaM <| Option (Expr × Expr) := do
  let nat := mkConst ``Nat
  let a ← mkFreshExprMVar nat
  let b ← mkFreshExprMVar nat
  let ineq ← mkAppM ``Nat.le #[a, b]
  if ← isDefEq ineq e then
    return some (a, b)
  else
    return none

elab "match_le" : tactic => withMainContext do
  match ← matchLe (← getMainTarget) with
  | some (a, b) =>
    logInfo m!"Matched inequality; a = {a}, b = {b}"
  | none =>
    logWarning m!"Main target not of the correct form"

elab "match_le_hyp" t:term : tactic =>
  withMainContext do
  let h ← elabTerm t none
  match ← matchLe (← inferType h) with
  | some (a, b) =>
    logInfo m!"Matched inequality; a = {a}, b = {b}"
  | none =>
    logWarning m!"Main target not of the correct form"

example (x y: Nat)(h : x ≤ y) : x ≤ y := by
  match_le
  match_le_hyp h
  assumption

elab "rw_le" t:term : tactic =>
  withMainContext do
    let h ← elabTerm t none
    let hType ← inferType h
    let target ← getMainTarget
    match ← matchLe hType, ← matchLe target with
    | some (a, b), some (c, d) =>
      let firstEq ← isDefEq a c
      let secondEq ← isDefEq b d
      if firstEq && secondEq then
        closeMainGoal `rw_le h
      else
      if firstEq then
        -- have `a = c`, so `h` is `c ≤ b` and we need `b ≤ d`
        let newTarget ← mkAppM ``Nat.le #[b, d]
        let newGoal ← mkFreshExprMVar newTarget
        let proof ← mkAppM ``Nat.le_trans #[h, newGoal]
        let goal ← getMainGoal
        goal.assign proof
        replaceMainGoal [newGoal.mvarId!]
      else
      if secondEq then
        -- have `b = d`, so `h` is `a ≤ d` and we need `c ≤ a`
        let newTarget ← mkAppM ``Nat.le #[c, a]
        let newGoal ← mkFreshExprMVar newTarget
        let proof ← mkAppM ``Nat.le_trans #[newGoal, h]
        let goal ← getMainGoal
        goal.assign proof
        replaceMainGoal [newGoal.mvarId!]
      else
        throwError "Neither ends matched"
    | _, _ =>
      throwError "Did not get inequalities"


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₁
    exact h₂

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₂
    exact h₁


example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
  by
    rw_le h₁
