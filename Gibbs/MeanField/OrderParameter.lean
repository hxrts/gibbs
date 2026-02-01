import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
# Order Parameters

An order parameter is a coarse-grained observable that distinguishes
macroscopic phases. The simplest example is the magnetization of a spin
system: the average value of a per-site observable. This file defines the
mean of a finite family, the magnetization induced by a per-site function,
and a general `OrderParameter` wrapper for use in both physics and consensus
applications.
-/

namespace Gibbs.MeanField

noncomputable section

open scoped BigOperators

variable {ι S : Type} [Fintype ι]

/-! ## Averages and Magnetization -/

/-- The mean of a finite family of real numbers. -/
def mean (f : ι → ℝ) : ℝ := by
  -- Normalize the sum by the number of indices.
  exact (∑ i, f i) / (Fintype.card ι : ℝ)

/-- Magnetization induced by a per-site observable `σ`. -/
def meanMagnetization (σ : S → ℝ) (state : ι → S) : ℝ := by
  -- Average the observable across sites.
  exact mean (fun i => σ (state i))

/-! ## Order-Parameter Wrapper -/

/-- An order parameter is a real-valued observable on global states. -/
structure OrderParameter (State : Type) where
  /-- The order-parameter value for a state. -/
  value : State → ℝ

/-- Magnetization as an order parameter on product states. -/
def magnetizationParameter (σ : S → ℝ) : OrderParameter (ι → S) := by
  -- Package the magnetization map as an order parameter.
  exact ⟨fun state => meanMagnetization (ι := ι) σ state⟩

end

end Gibbs.MeanField
