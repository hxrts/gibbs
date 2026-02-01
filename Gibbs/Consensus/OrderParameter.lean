import Gibbs.Consensus.Basic
import Gibbs.MeanField.OrderParameter

/-!
# Consensus order parameter

The magnetization `m(s) = (1/N) Σ σ_i` measures the degree of agreement in
a configuration, exactly as it measures spin alignment in an Ising model.
When `|m| ≈ 1` the system is in the ordered (consensus) phase. When
`|m| ≈ 0` it is disordered (no agreement). This file specializes the
mean-field order-parameter machinery to consensus configurations, making
the Ising/majority-vote correspondence formal.
-/

namespace Gibbs.Consensus

noncomputable section

open Gibbs.MeanField

/-! ## Consensus Order Parameters -/

/-- Magnetization on consensus configurations. -/
def magnetization {N : ℕ} {S : Type} (σ : S → ℝ) (cfg : Config N S) : ℝ := by
  -- Use the mean-field magnetization with `Process N` as the index type.
  exact MeanField.meanMagnetization (ι := Process N) σ cfg

/-- An order parameter on consensus configurations. -/
abbrev OrderParameter (N : ℕ) (S : Type) : Type :=
  MeanField.OrderParameter (Config N S)

/-- Magnetization packaged as a consensus order parameter. -/
def magnetizationParameter {N : ℕ} {S : Type} (σ : S → ℝ) : OrderParameter N S := by
  -- Reuse the mean-field constructor.
  exact MeanField.magnetizationParameter (ι := Process N) (S := S) σ

end

end Gibbs.Consensus
