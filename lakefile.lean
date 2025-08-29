import Lake
open Lake DSL

package «matroids» where
  moreServerArgs := #["-DwarningAsError=false"]
  -- add package configuration options here

@[default_target]
lean_lib «Matroids» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ s!"v{Lean.versionString}"
