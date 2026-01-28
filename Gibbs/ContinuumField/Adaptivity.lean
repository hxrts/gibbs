import Gibbs.ContinuumField.Basic
import Gibbs.ContinuumField.Kernel

/-
The Problem. We need a way to state how kernels depend on fields (ρ, p, ω)
with explicit regularity assumptions, and a place to describe deterministic
kernel evolution rules.

The difficulty is staying abstract while still pinning down the contracts
needed later for analysis. We introduce a field metric, a dependence structure,
and a drift-style evolution rule.

Solution Structure.
1. StateMetric: a metric-like structure on FieldState
2. KernelDependence: kernel-of-state + Lipschitz regularity
3. KernelDynamics: deterministic evolution equation for kernels
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
