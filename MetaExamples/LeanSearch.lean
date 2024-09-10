import Lean
import Mathlib
open Lean Meta Elab Tactic Parser Term

def getQueryJson (s: String)(num_results : Nat := 12) : IO <| Array Json := do
  let apiUrl := "https://leansearch.net/api/search"
  let s' := s.replace " " "%20"
  let q := apiUrl++ s!"?query={s'}&num_results={num_results}"
  let s ← IO.Process.output {cmd := "curl", args := #["-X", "GET", q]}
  let js := Json.parse s.stdout |>.toOption |>.get!
  return js.getArr? |>.toOption |>.get!

structure SearchResult where
  name : String
  type? : Option String
  docString? : Option String
  doc_url? : Option String
  kind? : Option String

namespace SearchResult

def ofJson? (js: Json) : Option SearchResult :=
  match js.getObjValAs? String "formal_name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "formal_type" |>.toOption
      let doc? := js.getObjValAs? String "docstring" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let docurl? := js.getObjValAs? String "doc_url" |>.toOption
      let kind? := js.getObjValAs? String "kind" |>.toOption
      some {name := name, type? := type?, docString? := doc?, doc_url? := docurl?, kind? := kind?}
  | _ => none

def query (s: String)(num_results : Nat := 12) :
    IO <| Array SearchResult := do
  let jsArr ← getQueryJson s num_results
  return jsArr.filterMap ofJson?

def toCommandSuggestion (sr : SearchResult) : TryThis.Suggestion :=
  let data := match sr.docString? with
    | some doc => s!"{doc}\n"
    | none => ""
  -- let data := data ++ match sr.type? with
  --   | some type => s!"· Type: {type}\n"
  --   | none => ""
  -- let data := data ++ match sr.doc_url? with
  --   | some docurl => s!"· URL: {docurl}\n"
  --   | none => ""
  {suggestion := s!"#check {sr.name}", postInfo? := sr.type?.map fun s => s!" -- {s}" ++ s!"\n{data}"}

def toTermStx? (sr: SearchResult) : MetaM <| Option Syntax :=
  sr.type?.bindM fun type => do
  let term? := runParserCategory (← getEnv) `term type
  return term?.toOption

def toTermSuggestion (sr: SearchResult) : TryThis.Suggestion :=
  match sr.type? with
  | some type => {suggestion := sr.name, postInfo? := some s!" (type: {type})"}
  | none => {suggestion := sr.name}

def toTermSuggestions (sr: SearchResult) : Array TryThis.Suggestion :=
  match sr.type? with
  | some type => #[{suggestion := sr.name, postInfo? := some s!" (type: {type})"}, {suggestion := type, preInfo? := some "Type: "}, {suggestion := s!"({sr.name} : {type})"}]
  | none => #[{suggestion := sr.name}]

def toTacticSuggestions (sr: SearchResult) : Array TryThis.Suggestion :=
  match sr.type? with
  | some type => #[{suggestion := s!"apply {sr.name}"},
        {suggestion := s!"have : {type} := {sr.name}"},
        {suggestion := s!"rw [{sr.name}]"},
        {suggestion := s!"rw [← {sr.name}]" }]
  | none => #[]

end SearchResult

def getQueryCommandSuggestions (s: String)(num_results : Nat := 12) :
  IO <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map SearchResult.toCommandSuggestion

def getQueryTermSuggestions (s: String)(num_results : Nat := 12) :
  IO <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map SearchResult.toTermSuggestion

def getQueryTacticSuggestions (s: String)(num_results : Nat := 12) :
  IO <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map SearchResult.toTacticSuggestions |>.join

def getQueryTacticSuggestionGroups (s: String)(num_results : Nat := 12) :
  IO <| Array (String ×  Array TryThis.Suggestion) := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map fun sr =>
      let fullName := match sr.type? with
        | some type => s!"{sr.name} (type: {type})"
        | none => sr.name
      (fullName, sr.toTacticSuggestions)

def defaultTerm (expectedType? : Option Expr) : MetaM Expr := do
  match expectedType? with
  | some type =>
    if !type.hasExprMVar then
      mkAppM ``sorryAx #[type, mkConst ``false]
    else
      return mkConst ``True.intro
  | none => return mkConst ``True.intro

def checkTactic (target: Expr)(tac: Syntax):
  TermElabM (Option Nat) :=
    withoutModifyingState do
    try
      let goal ← mkFreshExprMVar target
      let (goals, _) ←
        withoutErrToSorry do
        Elab.runTactic goal.mvarId! tac
          (← read) (← get)
      return some goals.length
    catch _ =>
      return none

open Command
syntax (name := lean_search_cmd) "#lean_search" str : command
@[command_elab lean_search_cmd] def leanSearchImpl : CommandElab :=
  fun stx => Command.liftTermElabM do
  match stx with
  | `(command| #lean_search $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← getQueryCommandSuggestions s
      TryThis.addSuggestions stx suggestions (header:= "Lean Search Results")
    else
      logWarning "Lean search query should end with a full stop (period) or a question mark."
  | _ => throwUnsupportedSyntax

syntax (name := lean_search_term) "lean_search#" str : term
@[term_elab lean_search_term] def leanSearchTermImpl : TermElab :=
  fun stx expectedType? => do
  match stx with
  | `(lean_search# $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let suggestions ← getQueryTermSuggestions s
      TryThis.addSuggestions stx suggestions (header:= "Lean Search Results")
    else
      logWarning "Lean search query should end with a full stop (period) or a question mark."
    defaultTerm expectedType?
  | _ => throwUnsupportedSyntax

syntax (name := lean_search_tactic) "lean_search?" str : tactic
@[tactic lean_search_tactic] def leanSearchTacticImpl : Tactic :=
  fun stx => withMainContext do
  match stx with
  | `(tactic|lean_search? $s) =>
    let s := s.getString
    if s.endsWith "." || s.endsWith "?" then
      let target ← getMainTarget
      let suggestionGroups ← getQueryTacticSuggestionGroups s
      for (name, sg) in suggestionGroups do
        let sg ←  sg.filterM fun s =>
          let sugTxt := s.suggestion
          match sugTxt with
          | .string s => do
            logInfo m!"Checking tactic: {s}"
            logInfo m!"Target: {← getMainTarget}"
            let stx? := runParserCategory (← getEnv) `tactic s
            match stx? with
            | Except.ok stx =>
              let n? ← checkTactic target stx
              return n?.isSome
            | Except.error e =>
              logInfo m!"Error: {e} while obtaining syntax tree"
              pure false
          | _ => pure false
        TryThis.addSuggestions stx sg (header:= s!"From: {name}")
    else
      logWarning "Lean search query should end with a full stop (period) or a question mark."
  | _ => throwUnsupportedSyntax

-- example := lean_search# "There are infinitely many odd numbers."
/-!
# Lean Search Examples

An example of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.
-/

#lean_search "There are infinitely many odd numbers"

example := lean_search# "There are infinitely many odd numbers"

example : 3 ≤ 5 := by
  lean_search? "If a natural number n is less than m, then the successor of n is less than the successor of m."
  sorry

open Parser
#check Parser
