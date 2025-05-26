import Lake
open Lake DSL

package «MOP» {
  Chapter_1.lean := #[`Mathlib]
}

@[default_target]
lean_lib «MOP» {
  dependencies := #[`Mathlib]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "main"
