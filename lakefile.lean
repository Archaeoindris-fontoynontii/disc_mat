import Lake
open Lake DSL

package «disc_mat» {
  -- add package configuration options here
}

lean_lib «DiscMat» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «disc_mat» {
  root := `Main
}
