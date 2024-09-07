import Lean
import MetaExamples.Basic
open Lean Meta Elab Tactic

/-!
## Checking tactics

We write a function to correctly check if a tactic closes a goal.
-/

#check Elab.runTactic

def checkTactic (target: Expr)(tac: Syntax):
  TermElabM (Option Nat) :=
    withoutModifyingState do
    try
      let goal ← mkFreshExprMVar target
      let (goals, _) ←
        Elab.runTactic goal.mvarId! tac
          (← read) (← get)
      return some goals.length
    catch _ =>
      return none

elab "check_tactic" tac:tacticSeq : tactic => do
  let n? ← checkTactic (← getMainTarget) tac
  match n? with
  | some n =>
    logInfo m!"Tactic succeeded; {n} goals remain"
  | none =>
    logWarning m!"Tactic failed"

example : 1 ≤ 5 := by
  check_tactic rfl
  check_tactic decide
  decide

syntax (name := check_tactic) "check_tactic?" tacticSeq : tactic
@[tactic check_tactic] def checkTacticImpl : Tactic := fun stx => do
 match stx with
 | `(tactic| check_tactic? $tac) =>
  let n? ← checkTactic (← getMainTarget) tac
  match n? with
  | some n =>
    logInfo m!"Tactic succeeded; {n} goals remain"
    TryThis.addSuggestion stx tac
  | none =>
    logWarning m!"Tactic failed"
 | _ => throwUnsupportedSyntax

example : 1 ≤ 5 := by
  check_tactic? rfl
  decide
