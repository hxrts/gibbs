import Lake
open Lake DSL

/-! # Gibbs Lean Package

Lake build definition for the Gibbs verification library.
Mean-field theory meets multiparty session types.

Uses shared mathlib from ../lean_common/mathlib4 to avoid rebuilding.
-/

package gibbs

-- Use shared local mathlib installation (with pre-built artifacts)
require mathlib from "../lean_common/mathlib4"
-- Effects spatial system from the local rumpsteak-aura repo
require rumpsteakLean from "../rumpsteak-aura/lean"

/-- Main library for mean-field session types formalization. -/
@[default_target]
lean_lib Gibbs where
  globs := #[`Gibbs.*]
