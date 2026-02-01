import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-
The Problem. We need a lightweight, application-agnostic order-parameter
interface for finite systems so consensus can later reuse it.

Solution Structure.
1. Define the mean value of a finite family of reals.
2. Define magnetization from a per-site observable.
3. Package order parameters as functions on states.
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
