import Lean
import MetaExamples.Basic
open Lean Meta Elab Term

partial def negate (e: Expr) : MetaM Expr := do
  match e with
  | .forallE name domain body bi => do
    if ← isProp domain then
      let negBody ← negate body
      mkAppM ``And #[domain, negBody]
    else
    let negFn ←
      withLocalDecl name bi domain fun x => do
        let negBody ← negate (body.instantiate1 x)
        mkLambdaFVars #[x] negBody
    mkAppM ``Exists #[negFn]
  | _ =>
    match e.app2? ``Exists with
    | some (_, .lam name domain body bi) => do
      withLocalDecl name bi domain fun x => do
        let negBody ← negate (body.instantiate1 x)
        mkForallFVars #[x] negBody
    | _ => mkAppM ``Not #[e]

elab "negate#" t:term : term => do
  let p ← elabType t
  negate p

#check negate# (∀n: Nat, n > 0 →  n ≠ n + 1)
#check negate# (∃n: Nat, 2 * n > n + 1)
#check fun (f: Nat → Nat) => negate# (∀ k : Nat, ∃ n: Nat, ∀ m: Nat, m > n → f m > k)

#check Not

#expr [∃ n:Nat, 2 * n > n + 1]
