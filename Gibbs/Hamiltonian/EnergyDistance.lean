import Mathlib.Data.ENNReal.Basic

/-
The Problem. We need an application-agnostic notion of distance that can
represent energy barriers and corruption budgets without committing to a
specific model.

Solution Structure.
1. Define a lightweight pseudometric valued in `ℝ≥0∞`.
2. Provide a basic ball construction for later specializations.
-/

namespace Gibbs.Hamiltonian

open scoped ENNReal

/-! ## Energy-Barrier Distance -/

/-- A pseudometric valued in `ℝ≥0∞`, intended to model energy barriers. -/
class EnergyDistance (α : Type) where
  /-- Distance between states. -/
  dist : α → α → ℝ≥0∞
  /-- Distance from a point to itself is zero. -/
  dist_self : ∀ x, dist x x = 0
  /-- Symmetry of the distance. -/
  dist_comm : ∀ x y, dist x y = dist y x
  /-- Triangle inequality. -/
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

/-- The energy-distance ball centered at `x` with radius `r`. -/
def edistBall {α : Type} [EnergyDistance α] (x : α) (r : ℝ≥0∞) : Set α := by
  -- A point is in the ball if its distance to `x` is at most `r`.
  exact { y | EnergyDistance.dist x y ≤ r }

/-- Self-distance is zero (re-exported for convenience). -/
theorem edist_self {α : Type} [EnergyDistance α] (x : α) :
    EnergyDistance.dist x x = 0 := by
  -- Use the class field directly.
  exact EnergyDistance.dist_self x

end Gibbs.Hamiltonian
