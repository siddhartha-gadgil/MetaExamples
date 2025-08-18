import Lean

open Lean Meta Elab Command Syntax Term Parser

def isProd? (e: Expr) : MetaM (Option <| Expr × Expr) := do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let u := mkSort <| Level.succ u
  let v := mkSort <| Level.succ v
  let α ← mkFreshExprMVar u
  let β ← mkFreshExprMVar v
  let x ←  mkFreshExprMVar α
  let y ←  mkFreshExprMVar β
  let p ← mkAppM ``Prod.mk #[x, y]
  if ← isDefEq p e then
    return some (x, y)
  return none

partial def kv? (e: Expr)  : MetaM (Option <| Name × Expr) := do
  match ← isProd? e with
  | some (kExpr, v) => do
    let α ← inferType kExpr
    unless ← isDefEq α (mkConst ``Name) do
      return none
    let key ← unsafe evalExpr Name (mkConst ``Name) kExpr
    return (key, v)
  | none => do
    return none

partial def kvs? (e: Expr) : MetaM (Std.HashMap Name Expr) := do
  match ←  kv? e with
  | some (key, value) => do
    let mut result := Std.HashMap.empty
    result := result.insert key value
    return result
  | none => do
    match ← isProd? e with
    | some (head, tail) => do
      match ← kv? head with
      | some (key, value) => do
        let mut result ← kvs? tail
        result := result.insert key value
        return result
      | none => do
        return Std.HashMap.empty
    | none => do
      return Std.HashMap.empty

-- from batteries
def getExplicitArgsFromType : Expr → Array Name → Array Name
  | .forallE n _ body bi, args =>
    getExplicitArgsFromType body <| if bi.isExplicit then args.push n else args
  | _, args => args

def fillFuncKWArgs (f: Expr) (kwArgs : Std.HashMap Name Expr) : TermElabM Expr := do
  let mut args : Array Expr := #[]
  let explNames := getExplicitArgsFromType (← inferType f) #[]
  for n in explNames do
    match kwArgs.get? n with
    | some v => args := args.push v
    | none => return f
  Term.synthesizeSyntheticMVarsNoPostponing
  mkAppM' f args

elab f:term "(**" kw:term ")" : term => do
  let f ←
    withoutPostponing do elabTerm f none
  let kw ←
    withoutPostponing do elabTerm kw none
  let kwArgs ← kvs? kw
  fillFuncKWArgs f kwArgs

def kwargsEg := ((`a, 1), (`b, 2), (`x, "hello"))

def f (a b :Nat) := a + b
#eval f (** ((`a, 1), (`b, 2), (`x, "hello"))) -- 3
#eval f (** kwargsEg) -- 3


syntax assgn := ident " := " term
syntax (name:=kwargs) "{" assgn,* "}" : term

def kwTerm : TSyntax ``assgn → MacroM Syntax.Term
  | `(assgn| $n:ident := $v:term) => do
    let n := quoteNameMk n.getId
    `(($n, $v))
  | _ => throw Lean.Macro.Exception.unsupportedSyntax

macro_rules
| `({ $p:assgn }) =>
    kwTerm p
| `({ $as:assgn,*, $last:assgn }) => do
    let head ← kwTerm last
    let tailPairs ← Array.mapM kwTerm as
    let stx ← tailPairs.foldrM (init := head) (fun acc p => `(($acc, $p)))
    return stx

#eval f (** kwargsEg) -- 3

def kwArgsEg' := { a := 1, b := 2, c := "hello" }

def sEg : Nat × Nat := {fst := 1, snd := 2}
#eval sEg -- (1, 2)

#eval kwargsEg
#eval kwArgsEg'

#eval f (** kwArgsEg')
#eval f (** { a := 1, b := 2, c := "hello" }) -- 3

-- Older test code

elab "read_key_val" t:term : term => do
  let t ←
    withoutPostponing do
    elabTerm t none
  let result ← kv? t
  match result with
  | some (key, value) => do
    logInfo m!"Key: {key}, Value: {value}"
    return t
  | none => do
    logInfo m!"Not a key-value pair"
    return t

#check read_key_val (`a, (1: Nat))

elab "read_key_vals" t:term : term => do
  let t ←
    withoutPostponing do
    elabTerm t none
  let result ← kvs? t
  let l := result.toList
  for (k, v) in l do
    logInfo m!"Key: {k}, Value: {v}"
  return t

#check read_key_vals ((`a, 1), (`b, 2), (`x, "hello"))


#check kwargsEg

example : Nat × Nat := {fst := 1, snd := 2}

#eval quoteNameMk `hello
#check kwargsEg
