import Lean
open Lean Meta Elab Tactic

/-!
### Next example: `le_rw`

We now give a more substantial example. This can be done with just macros, but we will use metaprogramming to illustrate the principles.

The tactic `rw_le h` works if the goal is of the form `a ≤ b` and `h` is a proof of `c ≤ d`, with `a`, `b`, `c` and `d` all natural numbers. If `a = c` or `b = d` or both, then it rewrites the goal.

Our first step is to recognize when an expression (for example the goal) is of the correct form.
-/
#check Expr.eq?
#check Expr.app2?

#check Nat.le

def matchLe (e: Expr) : MetaM (Option (Expr × Expr)) :=
  do
  let nat := mkConst ``Nat
  let a ← mkFreshExprMVar nat
  let b ← mkFreshExprMVar nat
  let e' ←  mkAppM ``Nat.le #[a, b]
  if ← isDefEq e e' then
    return some (a, b)
  else
    return none

elab "match_le" : tactic => withMainContext do
  let e ← getMainTarget
  let e' ← matchLe e
  match e' with
  | some (a, b) => logInfo m!"Inequality: {a} ≤ {b}"
  | none => logWarning "Not a ≤ b for natural numbers"
  return ()

elab "match_le_hyp" t:term : tactic => withMainContext do
  let e'' ← elabTerm t none
  let e ← inferType e''
  let e' ← matchLe e
  match e' with
  | some (a, b) => logInfo m!"Inequality: {a} ≤ {b}"
  | none => logWarning "Not a ≤ b for natural numbers"
  return ()

example (x y : Nat) (h : x ≤ y) : x ≤ y :=
  by
    match_le
    match_le_hyp h
    assumption

elab "rw_le" t:term : tactic => withMainContext do
  let e ← Tactic.elabTerm t none
  let p₁? ← matchLe <| ← inferType e
  let p₂? ← matchLe (← getMainTarget)
  match p₁?, p₂? with
  | some (a₁, b₁), some (a₂, b₂) => do
    let left_match ← isDefEq a₁ a₂
    let right_match ← isDefEq b₁ b₂
    if left_match && right_match then
      closeMainGoal `rw_le e
    else
    if left_match then
      let newGoal ← mkFreshExprMVar <| ← mkAppM ``Nat.le #[b₁, b₂]
      let trans ← mkAppM ``Nat.le_trans #[e, newGoal]
      let goal ← getMainGoal
      goal.assign trans
      replaceMainGoal [newGoal.mvarId!]
    else
    if right_match then
      let ineq ← mkFreshExprMVar <| ← mkAppM ``Nat.le #[a₂, a₁]
      let trans ← mkAppM ``Nat.le_trans #[ineq, e]
      let goal ← getMainGoal
      goal.assign trans
      replaceMainGoal [ineq.mvarId!]
    else
      logError "Endpoints do not match on either side"
      throwAbortTactic
  | _, _ =>
    logError m!"Could not rewrite as not inequalities {e} {← getMainTarget}"
    throwAbortTactic



example (x y : Nat) (h : x ≤ y) : x ≤ y :=
  by
    match_le
    assumption

/-!
We now write the tactic `rw_le` that rewrites.
-/

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  by
    rw_le h₂
    assumption

example (x y z : Nat) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ y :=
  by
    rw_le h₁
