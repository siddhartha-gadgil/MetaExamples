import MetaExamples.Basic
open Lean Meta

#eval 1 + 3

#check fun n: Nat ↦ n + 1

#eval (fun n: Nat ↦ n + 1) 3

/-
inductive Lean.Syntax : Type
number of parameters: 0
constructors:
Lean.Syntax.missing : Syntax
Lean.Syntax.node : SourceInfo → SyntaxNodeKind → Array Syntax → Syntax
Lean.Syntax.atom : SourceInfo → String → Syntax
Lean.Syntax.ident : SourceInfo → Substring → Name → List Syntax.Preresolved → Syntax
-/
#print Syntax

#stx [1]
#stx [1 + 2]
#stx [fun n : Nat ↦ n + 1]

#expr [(1: Nat) + 2]
#expr [fun n: Nat ↦ n + 1]
/-
inductive Lean.Expr : Type
number of parameters: 0
constructors:
Lean.Expr.bvar : Nat → Expr
Lean.Expr.fvar : FVarId → Expr
Lean.Expr.mvar : MVarId → Expr
Lean.Expr.sort : Level → Expr
Lean.Expr.const : Name → List Level → Expr
Lean.Expr.app : Expr → Expr → Expr
Lean.Expr.lam : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.forallE : Name → Expr → Expr → BinderInfo → Expr
Lean.Expr.letE : Name → Expr → Expr → Expr → Bool → Expr
Lean.Expr.lit : Literal → Expr
Lean.Expr.mdata : MData → Expr → Expr
Lean.Expr.proj : Name → Nat → Expr → Expr
-/
#print Expr
