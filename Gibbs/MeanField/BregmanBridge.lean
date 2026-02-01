import Gibbs.Hamiltonian.Legendre
import Gibbs.MeanField.ODE

/-!
# Bregman-Lyapunov Bridge

Packages the Bregman divergence from the Hamiltonian layer as a Lyapunov function
for MeanField ODE stability. This bridge file exists to keep the Hamiltonian layer
free of MeanField dependencies while still connecting the two.
-/

namespace Gibbs.MeanField

open Gibbs.Hamiltonian

noncomputable section

variable {n : ℕ}

/-- Conversion from `Fin n -> R` to `Config n`. -/
private def toConfig (x : Fin n → ℝ) : Config n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm x

/-- Conversion from `Config n` to `Fin n -> R`. -/
private def fromConfig (x : Config n) : Fin n → ℝ :=
  (EuclideanSpace.equiv (Fin n) ℝ) x

/-- Round-trip: `fromConfig (toConfig x) = x`. -/
private theorem fromConfig_toConfig (x : Fin n → ℝ) : fromConfig (toConfig x) = x := by
  simpa [fromConfig, toConfig] using
    (ContinuousLinearEquiv.apply_symm_apply (EuclideanSpace.equiv (Fin n) ℝ) x)

/-- Round-trip: `toConfig (fromConfig x) = x`. -/
private theorem toConfig_fromConfig (x : Config n) : toConfig (fromConfig x) = x := by
  simp [fromConfig, toConfig]

/-- Bregman positivity away from the equilibrium. -/
private theorem bregman_pos_of_ne {f : Config n → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    {x y : Config n} (hxy : x ≠ y) :
    0 < bregman f x y := by
  have hnonneg : 0 ≤ bregman f x y := bregman_nonneg hconv.convexOn hdiff x y
  have hzero : bregman f x y = 0 ↔ x = y := bregman_eq_zero_iff hconv hdiff x y
  have hne : bregman f x y ≠ 0 := by
    intro h
    exact hxy (hzero.mp h)
  exact lt_of_le_of_ne hnonneg (by simpa [ne_comm] using hne)

/-- Convert inequality at function level to configuration inequality. -/
private theorem toConfig_ne_of_ne {x : Fin n → ℝ} {x_eq : Config n}
    (hx : x ≠ fromConfig x_eq) : toConfig x ≠ x_eq := by
  intro hxeq
  have hx' : x = fromConfig x_eq := by
    have := congrArg fromConfig hxeq
    simpa [fromConfig_toConfig] using this
  exact hx hx'

/-- Package Bregman divergence as a Lyapunov function for MeanField stability.
    The monotonicity along trajectories is supplied as an assumption. -/
def bregman_lyapunov_data {f : Config n → ℝ}
    (hconv : StrictConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f)
    (x_eq : Config n)
    (F : DriftFunction (Fin n))
    (hcont : Continuous fun x => bregman f (toConfig x) x_eq)
    (hdec : ∀ (sol : ℝ → Fin n → ℝ),
      (∀ t ≥ 0, HasDerivAt sol (F (sol t)) t) →
      ∀ t₁ t₂, 0 ≤ t₁ → t₁ ≤ t₂ →
        bregman f (toConfig (sol t₂)) x_eq ≤ bregman f (toConfig (sol t₁)) x_eq) :
    LyapunovData F (fromConfig x_eq) := by
  refine
    { V := fun x => bregman f (toConfig x) x_eq
      V_cont := hcont
      V_zero := ?_
      V_pos := ?_
      V_nonneg := ?_
      V_decreasing := ?_ }
  · simpa [fromConfig, toConfig] using (bregman_self f x_eq)
  · intro x hx
    exact bregman_pos_of_ne hconv hdiff (toConfig_ne_of_ne hx)
  · intro x
    exact bregman_nonneg hconv.convexOn hdiff (toConfig x) x_eq
  · intro sol hsol t₁ t₂ ht₁ ht₁₂
    exact hdec sol hsol t₁ t₂ ht₁ ht₁₂

end

end Gibbs.MeanField
