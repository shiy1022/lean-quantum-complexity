import Lake
open Lake DSL

package «qma_amplification» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib «Definitions» where
  globs := #[.submodules `Definitions]

lean_lib «Theorems» where
  globs := #[.submodules `Theorems]
