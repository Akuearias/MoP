import Lake
open Lake DSL

package «MoP» {
  -- Lean version will be inferred automatically
  -- you can also set `leanVersion := "4.5.0"`
  -- if you want to pin it
}

lean_lib «MOP» {
  -- optional: config options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

--require math2001_course from git
--  "https://github.com/hrmacbeth/math2001.git" @ "main"
