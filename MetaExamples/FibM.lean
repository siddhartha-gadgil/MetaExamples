import Batteries
import MetaExamples.State
open Batteries State

/-!
## The `FibM` State Monad
-/
abbrev FibM := StateM (HashMap Nat Nat)
/-!
* We have a background state that is a `HashMap Nat Nat`, to store values already computed.
* When computing a term of type `FibM α` we can `get` and use the state and also `set` or `update` it.
* Future computations automatically use the updated state.
* Using this we can efficiently compose.
-/


def fibM (n: Nat) : FibM Nat := do
  let s ← get
  match s.find? n with
  | some y => return y
  | none =>
    match n with
    | 0 => return 1
    | 1 =>  return 1
    | k + 2 => do
      let f₁ ← fibM k
      let f₂ ← fibM (k + 1)
      let sum := f₁ + f₂
      let m ← get
      set <| m.insert n sum
      return sum

#eval fibM 32 |>.run' {}
