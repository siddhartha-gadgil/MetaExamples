import Lean
import MetaExamples.Basic
open Lean Meta Elab Tactic

/-!
## Checking tactics

-/

/-
⊢ MVarId →
  Syntax →
    optParam Term.Context
        { declName? := none, auxDeclToFullName := ∅, macroStack := [], mayPostpone := true, errToSorry := true,
          autoBoundImplicit := false,
          autoBoundImplicits :=
            { root := PersistentArrayNode.node (Array.mkEmpty PersistentArray.branching.toNat),
              tail := Array.mkEmpty PersistentArray.branching.toNat, size := 0, shift := PersistentArray.initShift,
              tailOff := 0 },
          autoBoundImplicitForbidden := fun x ↦ false, sectionVars := ∅, sectionFVars := ∅, implicitLambda := true,
          heedElabAsElim := true, isNoncomputableSection := false, ignoreTCFailures := false, inPattern := false,
          tacticCache? := none, tacSnap? := none, saveRecAppSyntax := true, holesAsSyntheticOpaque := false } →
      optParam Term.State
          { levelNames := [], syntheticMVars := ∅, pendingMVars := ∅, mvarErrorInfos := [], mvarArgNames := ∅,
            letRecsToLift := [] } →
        MetaM (List MVarId × Term.State)
-/
#check Elab.runTactic

def checkTactic (target : Expr) (tac : Syntax) : TermElabM (Option Nat) :=
  withoutModifyingState do
    let goal ← mkFreshExprMVar target
    try
      let (goals, _) ← runTactic goal.mvarId! tac (← read) (← get)
      return some goals.length
    catch _ =>
      return none

elab "check_tactic" tac:tacticSeq : tactic => do
    let n? ← checkTactic (← getMainTarget) tac
    match n? with
    | some k => logInfo m!"Tactic succeeded; goals remaining: {k}"
    | none => logWarning "Tactic failed"

example : 1 ≤ 3 := by
    check_tactic rfl
    check_tactic decide
    decide
