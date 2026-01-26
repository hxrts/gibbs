import Lake
open Lake DSL

/-! # Gibbs Lean Package

Lake build definition for the Gibbs verification library.
Mean-field theory meets multiparty session types.
-/

package gibbs

-- Mathlib provides standard lemmas and automation for proofs.
-- Pin to a mathlib tag that matches the Lean toolchain.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

-- Pin Mathlib's transitive dependencies to tested versions
-- (prevents Lake from resolving to newer incompatible versions)
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "24241822"
require Qq from git
  "https://github.com/leanprover-community/quote4" @ "93125039"
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "2f6d2387"
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4" @ "b4fb2aa5"
require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "933fce7e"
require importGraph from git
  "https://github.com/leanprover-community/import-graph" @ "e9f31324"
require LeanSearchClient from git
  "https://github.com/leanprover-community/LeanSearchClient" @ "3591c3f6"
require plausible from git
  "https://github.com/leanprover-community/plausible" @ "160af9e8"

/-- Main library for mean-field session types formalization. -/
@[default_target]
lean_lib Gibbs where
  globs := #[`Gibbs.*]
