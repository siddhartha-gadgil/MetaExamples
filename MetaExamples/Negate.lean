import Lean
import MetaExamples.Basic
open Lean Meta Elab Term

/-!
## Negating expressions

In this example, we define a function `negate` that takes a proposition `p` and returns its negation. This is a refinement of the `Not` function in Lean using
`¬ ∀ x : α, P x = ∃ x : α, ¬ P x` and
`¬ ∃ x : α, P x = ∀ x : α, ¬ P x`.
-/

#check Exists

partial def negate (e: Expr) : MetaM Expr := do
  match e with
  | .forallE name domain body bi =>
    if ← isProp domain then
    withLocalDecl name bi domain fun x => do
      let body := body.instantiate1 x
      mkAppM ``And #[domain, ← negate body]
    else
    let negFn ←
    withLocalDecl name bi domain fun x => do
      let body := body.instantiate1 x
      let negBody ← negate body
      mkLambdaFVars #[x] negBody
    mkAppM ``Exists #[negFn]
  | _ =>
    match e.app2? ``Exists with
    | some (_, .lam name domain body bi) =>
      withLocalDecl name bi domain fun x => do
        let body := body.instantiate1 x
        let negBody ← negate body
        mkForallFVars #[x] negBody
    | _ =>
      mkAppM ``Not #[e]

elab "negate#" t:term : term => do
  let p ← elabType t
  negate p

#check negate# (∀n: Nat, n ≠ n + 1)
#check negate# (∀n: Nat, n > 0 →  n ≠ n + 1)
#check negate# (∃n: Nat, 2 * n > n + 1)
#check fun (f: Nat → Nat) => negate# (∀ k : Nat, ∃ n: Nat, ∀ m: Nat, m > n → f m > k)

#expr [∃ n:Nat, 2 * n > n + 1]
#check Expr.app2?
