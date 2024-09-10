import Lean
import Cache.IO
import Mathlib
open Lean Meta Elab Tactic Cache.IO

def getQueryJson (s: String)(num_results : Nat := 12) : IO <| Array Json := do
  let apiUrl := "https://leansearch.net/api/search"
  let s' := s.replace " " "%20"
  let q := apiUrl++ s!"?query={s'}&num_results={num_results}"
  let s ← runCurl #["-X", "GET", q]
  let js := Json.parse s |>.toOption |>.get!
  return js.getArr? |>.toOption |>.get!

def getCommandSuggestion (js: Json) : Option TryThis.Suggestion :=
  match js.getObjValAs? String "formal_name" with
  | Except.ok name =>
      let type? := js.getObjValAs? String "formal_type" |>.toOption
      let doc? := js.getObjValAs? String "docstring" |>.toOption
      let doc? := doc?.filter fun s => s != ""
      let docurl? := js.getObjValAs? String "doc_url" |>.toOption
      let docurl := (docurl?.map fun s => s!" (link: {s})").getD ""
      some {suggestion := s!"#check {name}", postInfo? := type?.map fun s => s!" -- {s}", preInfo? := doc?.map fun doc => s!"/- {doc}{docurl}-/\n"}
  | _ => none

def getQueryCommandSuggestions (s: String)(num_results : Nat := 6) :
  IO <| Array TryThis.Suggestion := do
    let jsArr ← getQueryJson s num_results
    return jsArr.filterMap getCommandSuggestion

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
  | _ => throwUnsupportedSyntax

#lean_search "There are infinitely many prime numbers"
