/-!
## Naive Fibonacci numbers

The following definition is infamously slow as values are repeatedly computed
-/
def fib : Nat → Nat
| 0 => 1
| 1 => 1
| k + 2 => fib k + fib (k + 1)

-- #eval fib 32
