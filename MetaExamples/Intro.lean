import MetaExamples.Basic
open Lean Meta

/-!
# Meta-programming

* Meta-programming is writing functions/programs that *work with* programs or their components.
* The principled way to do this is to work with **internal representations** of program components.
* In Lean, there are two levels of internal representation, `Syntax` and `Expr`.
* Code is processed in two steps, **Parsing** transforms text to `Syntax` and **Elaboration** transforms `Syntax` (for terms) to `Expr`.
-/
#eval 1 + 3

#check fun n: Nat ↦ n + 1

#eval (fun n: Nat ↦ n + 1) 3

/-!
## Syntax

* `Syntax` is an inductive type that gives a rooted tree structure.
* `Syntax` is flexible, can represent all sorts of stuff, and is extensible.
-/
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
#stx [1 + 3]
#stx [fun n : Nat ↦ n + 1]

/-!
## Expr

* `Expr` is an inductive type representing terms in the foundations of Lean.
-/

#expr [Nat]
#expr [Nat → Nat]
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
