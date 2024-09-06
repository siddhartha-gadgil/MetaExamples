import Lean

open Lean Meta Elab Tactic
/-!
## What is a Tactic?

A higly simplified view of a tactic is the following:

* `TacticM` is a **State Monad**, which means an element of `TacticM α` is a term of type `α` that depends on an initial state and also returns a final state, i.e. a term of type `Tactic.State → (α , Tactic.State)`.
* A tactic is an element of `TacticM Unit`.
* As a term of type `Unit` is unique (so has no information), a tactic is essentially a function that modifies the tactic state.
-/


#check getMainTarget -- TacticM Expr
#check getMainGoal -- TacticM MVarId

#check getGoals -- TacticM (List MVarId)
#check setGoals -- List MVarId → TacticM Unit
