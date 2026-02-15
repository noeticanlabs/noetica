import Lake
open Lake DSL

package CK0 where
  moreServerArgs := #["-Ktrace.Elab.definition.body=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib CK0
