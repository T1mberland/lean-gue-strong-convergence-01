import Lake
open Lake DSL

package «lean-gue-strong-convergence» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lean-free-prob» from git
  "https://github.com/T1mberland/lean-free-probability-01.git" @
    "fa4067d9fd8ea56d8e39651e9a7871538e4fb333"

require «lean-log-sobolev» from git
  "https://github.com/T1mberland/lean-log-sobolev.git" @
    "1a95157e7d4cc18d444aa640c751acbe4c7692d4"

@[default_target]
lean_lib GUEStrongConvergence

lean_lib GUEStrongConvergenceVerification
