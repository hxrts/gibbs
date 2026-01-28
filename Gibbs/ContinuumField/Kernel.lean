import Gibbs.ContinuumField.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-
The Problem. We need a kernel object that can live at the choreography level
and project to local kernel fields. The kernel must be measurable, nonnegative,
normalized, and (later) adaptive in a deterministic way.

The difficulty is stating these constraints without committing to a specific
space or dynamics. We parameterize by a measurable space and expose only the
properties we need for projection and operator semantics.

Solution Structure.
1. KernelField: local displacement kernel
2. GlobalKernel: full nonlocal kernel with properties
3. KernelRule: deterministic adaptive update
4. local: projection to a local kernel field
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

/-- Project a global kernel to a local kernel field at position x. -/
def localKernel (K : GlobalKernel X) (x : X) : KernelField X :=
  -- Use displacement coordinates ξ ↦ K(x, x + ξ)
  fun ξ => K.K x (x + ξ)

end GlobalKernel

end Gibbs.ContinuumField
