import Gibbs.ContinuumField.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Interaction kernels

A `GlobalKernel` `K(x, x')` encodes nonlocal interactions between spatial
positions, analogous to the coupling matrix `J_ij` in a lattice spin model
but defined on continuous space. It carries measurability, nonnegativity,
normalization, and integrability guarantees.

The key operation is *projection to displacement coordinates*: at each point
`x`, the local kernel field `ξ ↦ K(x, x+ξ)` captures how the interaction
strength varies with displacement. A `KernelRule` makes this adaptive by
allowing the kernel to depend deterministically on the current field state
`(ρ, p, ω)`.
-/

namespace Gibbs.ContinuumField

open scoped Classical
open MeasureTheory

/-! ## Kernel Types -/

/-- A local kernel field over displacements ξ. -/
abbrev KernelField (X : Type*) := X → ℝ  -- local kernel as a function

/-- A global kernel K(x, x') with normalization and measurability. -/
structure GlobalKernel (X : Type*) [MeasureTheory.MeasureSpace X] where
  /-- The kernel function K(x, x'). -/
  K : X → X → ℝ
  /-- Measurability in the product space. -/
  measurable_K : Measurable (fun p : X × X => K p.1 p.2)
  /-- Nonnegativity for all points. -/
  nonneg : ∀ x x', 0 ≤ K x x'
  /-- Normalization: integral over x' is 1 (or fixed strength). -/
  mass_one : ∀ x, ∫ x', K x x' = (1 : ℝ)
  /-- Integrability of K(x, ·) for each x. -/
  integrable_K : ∀ x, MeasureTheory.Integrable (fun x' => K x x')

/-- A deterministic adaptive rule that produces a kernel from field state. -/
structure KernelRule (X : Type*) (V : Type*) (W : Type*)
    [MeasureTheory.MeasureSpace X] where
  /-- Deterministic kernel update from (ρ, p, ω). -/
  next : FieldState X V W → GlobalKernel X

namespace GlobalKernel

variable {X : Type*} [MeasureTheory.MeasureSpace X] [Add X]
-- Only addition is needed for displacement coordinates; no inverses used.

/-- Project a global kernel to a local kernel field at position x. -/
def localKernel (K : GlobalKernel X) (x : X) : KernelField X :=
  -- Use displacement coordinates ξ ↦ K(x, x + ξ)
  fun ξ => K.K x (x + ξ)

end GlobalKernel

end Gibbs.ContinuumField
