import Gibbs.ContinuumField.Basic
import Gibbs.ContinuumField.Kernel

/-!
# Adaptive kernel dependence

In many continuum models the interaction kernel is not fixed but evolves
with the field state. For example, the effective coupling range may grow
as density increases, or anisotropy may develop in response to polarization.

`KernelDependence` formalizes this by pairing a kernel-of-state map with a
Lipschitz regularity bound: small changes in `(ρ, p, ω)` produce small
changes in the kernel. `KernelDynamics` provides a drift term for continuous-
time kernel evolution, `dK/dt = drift(ρ, p, ω)`.
-/

namespace Gibbs.ContinuumField

open scoped Classical

/-! ## State Metric -/

/-- A metric-like distance on field states. -/
structure StateMetric (X : Type*) (V : Type*) (W : Type*) where
  /-- Distance between two field states. -/
  dist : FieldState X V W → FieldState X V W → ℝ
  /-- Distances are nonnegative. -/
  dist_nonneg : ∀ s₁ s₂, 0 ≤ dist s₁ s₂

/-! ## Kernel Dependence -/

/-- A kernel depending on fields with explicit regularity. -/
structure KernelDependence (X : Type*) (V : Type*) (W : Type*)
    [MeasureTheory.MeasureSpace X] where
  /-- Kernel determined by the current fields. -/
  kernelOf : FieldState X V W → GlobalKernel X
  /-- State-space metric used for regularity. -/
  metric : StateMetric X V W
  /-- Lipschitz regularity in the field state. -/
  lipschitz : ∃ L ≥ 0, ∀ s₁ s₂ x x',
    |(kernelOf s₁).K x x' - (kernelOf s₂).K x x'| ≤ L * metric.dist s₁ s₂

/-! ## Kernel Dynamics -/

/-- A deterministic evolution rule: d/dt K = drift(ρ,p,ω). -/
structure KernelDynamics (X : Type*) (V : Type*) (W : Type*)
    [MeasureTheory.MeasureSpace X] where
  /-- Drift term for the kernel evolution equation. -/
  drift : FieldState X V W → X → X → ℝ

end Gibbs.ContinuumField
