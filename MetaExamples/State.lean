/-!
# State Monads

* If `s` is a type, then we have a **State Monad** `State s`.
* What this means is that if `α` is a type, then `State s α` is a type so that a term of this type:
  - takes an initial state as input
  - returns a term of type `α`,
  - and a final state.
* Thus, a term of type `State s α` is essentially a function `s → α × s`.
-/
structure State (s α: Type) where
  run : s → α × s

namespace State
def get : State s s := ⟨fun s => (s, s)⟩
def update (f: s → s) : State s Unit := ⟨fun s => ((), f s)⟩

def run'[Inhabited s](x: State s α) (s: s := default) : α := (x.run s).1
end State

instance : Monad (State s) where
  pure x := ⟨fun s => (x, s)⟩
  bind x f := ⟨fun s =>
    let (a, s') := x.run s
    (f a).run s'⟩
open State

instance [rep : Repr α][Inhabited s] : Repr (State s α) :=
  ⟨fun mx n => rep.reprPrec mx.run' n⟩
