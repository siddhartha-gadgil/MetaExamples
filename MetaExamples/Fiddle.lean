import Lean
import Mathlib
import Std.Internal.Async

open Lean Meta Elab Command Syntax Term Parser

elab "nat#" t:term : term => do
  let e ← elabTermEnsuringType t (mkConst ``Nat)
  -- logInfo m!"{e}"
  let mvars ← Term.collectUnassignedMVars e
  logInfo m!"{mvars}"
  return e

set_option pp.mvars.withType true in
#check nat# (Nat.add _ _)
#check nat# (Nat.add 1 _)
#check nat# (Nat.add 1 2)
#check nat# (Nat.add 1 ?x)

#check nat# (Nat.add (_ : Nat) ?x + (?y: Nat))

elab "type#" t:term : term => do
  let e ← elabType t
  -- logInfo m!"{e}"
  let mvars ← Term.collectUnassignedMVars e
  logInfo m!"Holes: {mvars.size}"
  for mvar in mvars do
    let mvar ← instantiateMVars mvar
    logInfo m!"Hole type: {← ppExpr <| ← inferType mvar}"
  let abs ← abstractMVars e
  return abs.expr

elab "term#" t:term : term => do
  let e ← elabTerm t none
  -- logInfo m!"{e}"
  let mvars ← Term.collectUnassignedMVars e
  logInfo m!"Holes: {mvars.size}"
  for mvar in mvars do
    let mvar ← instantiateMVars mvar
    logInfo m!"Hole type: {← ppExpr <| ← inferType mvar}"
  let abs ← abstractMVars e
  return abs.expr


/-
⊢ AbstractMVarsResult → MetaM (Array Expr × Array BinderInfo × Expr)
-/
#check openAbstractMVarsResult
#check lambdaMetaTelescope
#check lambdaTelescope

set_option pp.funBinderTypes true
#check type# (List _)
#check type# (List Nat)
#check type# (Vector _ _)
#check type# (_ × _)
#check type# (List (List Nat))
#check type# (List (List _))
#check type# (∀ (_: Nat), Prime _)
#check term# (∀(x : Nat), Prime x)
#check term# (Prime (?x : Nat))
#check term# (Prime (_ : Nat))
#check type# ((?a : Nat) = ?a)


/-
Lean.Elab.Term.collectUnassignedMVars (type : Expr) (init : Array Expr := #[])
  (except : MVarId → Bool := fun x ↦ false) : TermElabM (Array Expr)
-/
#check Term.collectUnassignedMVars

example : 1 ≤ 3 := Nat.succ_le_succ (Nat.zero_le _)

#check Lean.LocalContext.foldlM

example (n: Nat) : n + 2 ≤ n + 4 := by
  induction n
  · extract_goal using zero_eg
    sorry
  · extract_goal using step_eg
    sorry

theorem eg (n : ℕ) (m: ℕ) : n + 1 ≤ m + 3 := sorry

theorem eg' (m : ℕ) : m + 1 = m + 3 := by
  have eg (n : ℕ) : n + 1 = n + 3 := sorry
  apply eg

example : 1 = 1 := by exact?

theorem eg'' (m : ℕ) :  m + 1 ≤ m + 3 :=
  eg _ _

example (n: Nat): n ≤ n + 1 ∧ n + 1 ≤ n + 2 := by
  apply And.intro
  · extract_goal using eg₁
    sorry
  · extract_goal using eg₂
    sorry

theorem eg₁ (n : ℕ) : n ≤ n + 1 := by exact Nat.le_add_right n 1

example (n: ℕ) : n * n ≤ n * n + 1 := by apply eg₁

elab "#show_type" name:ident : command => do
  let decl ← getConstInfo name.getId
  logInfo m!"{decl.type}"

#show_type eg₁

#check Nat.rec
#check MVarId.apply
#check Eq.rec
#check Eq.ndrec
#check Expr.getAppFnArgs
#check mkAppM
#check Expr.eqOrIff?
#eval (default : Expr)
#print Nat.succ.injEq
#check Eq.casesOn

#check Eq.propIntro
#print Eq.casesOn
#check LE.mk
#check Exists.rec



open Lean.Parser.Term in
example (t: Syntax.Term) : MetaM Syntax.Tactic := do
  let l ← `(letIdBinder| (x : $t))
  let ls := #[l, l]
  `(tactic| have x $ls* := sorry)

#check Lean.Parser.Term.letIdBinder

open Tactic
elab "use_till" n:num "then" tac:tacticSeq : tactic => withMainContext do
  let n := n.getNat
  let s ← saveState
  for j in [0:n] do
    let s ← saveState
    try do
      let jLit := Syntax.mkNumLit <| toString j
      evalTactic <| ← `(tactic|use $jLit:term)
      evalTactic tac
      unless (← getGoals).isEmpty do
        throwError "tactic failed"
      return ()
    catch _ =>
      restoreState s
  restoreState s

example : ∃ n: Nat, n * n = 49 := by
  use_till 12 then try(rfl)

#check ((`a, 1), (`b, 2), (`x, "hello"))

#check Std.HashMap.ofList

#check mkFreshLevelMVar

open Std

open Std.Internal.IO.Async

def writeSlow : Async Unit := do
  IO.sleep 3000
  IO.FS.writeFile "slow.txt" "This is a slow write operation."

elab "#write_slow" : command =>
  do
  let _tsk ← writeSlow.toIO
  return

#write_slow

#check background
#check 1

#check Lean.CodeAction.CommandCodeAction
