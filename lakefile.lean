import Lake
open Lake DSL

package khachiyan

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0a6c8e0355da0405d616f80b9f8232c4fab2cc5b"

@[default_target]
lean_lib Khachiyan
