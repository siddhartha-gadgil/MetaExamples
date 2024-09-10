import Lean
import Mathlib
open Lean Meta Elab Tactic Parser

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
    | some doc => s!"· Description: {doc}\n"
    | none => ""
  let data := data ++ match sr.type? with
    | some type => s!"· Type: {type}\n"
    | none => ""
  let data := data ++ match sr.doc_url? with
    | some docurl => s!"· URL: {docurl}\n"
    | none => ""
  {suggestion := s!"#check {sr.name}", postInfo? := sr.type?.map fun s => s!" -- {s}" ++ s!"\n{data}"}

end SearchResult

def getQueryCommandSuggestions (s: String)(num_results : Nat := 12) :
  IO <| Array TryThis.Suggestion := do
    let searchResults ←  SearchResult.query s num_results
    return searchResults.map SearchResult.toCommandSuggestion

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

/-!
# Lean Search Command

An example of using the leansearch API. The search is triggered when the sentence ends with a full stop (period) or a question mark.
-/

#lean_search "There are infinitely many odd numbers"

#lean_search "delay task (use `Task.await`)"

open Parser
#check Parser
