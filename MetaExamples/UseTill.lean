import Lean
import Mathlib
open Lean Meta Elab Tactic

example : ∃ n: Nat, n * n = 64 := by
  use 8


/-!
## Example: `use_till`

We write a tactic that automatically tries a range of values
-/
elab "use_till" n:num "then" tac:tacticSeq : tactic =>
  withMainContext do
    let n := n.getNat
    let s₀ ← saveState
    for j in [0:n] do
      let s ← saveState
      try
        let jLit :=
          Syntax.mkNumLit <| toString j
        evalTactic <|
          ← `(tactic| use $jLit:term)
        if (← getGoals).isEmpty then
          return
        evalTactic tac
        unless (← getGoals).isEmpty do
          throwError "goals remain"
        return
      catch _ =>
        restoreState s
    restoreState s₀
    throwError "All tactics failed"

example : ∃ n: Nat, n * n = 64 := by
  use_till 10 then simp
