import Lake
open Lake DSL

package "MetaExamples" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ "git#v4.22.0"

require "leanaidecore" from git "https://github.com/siddhartha-gadgil/LeanAide.git" @ "main" / "LeanAideCore"

@[default_target]
lean_lib «MetaExamples» where
  -- add any library configuration options here

lean_exe concegs where
