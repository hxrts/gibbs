import Gibbs.Hamiltonian.Basic
import Gibbs.Hamiltonian.ConvexHamiltonian
import Gibbs.Hamiltonian.DampedFlow

/-
The Problem. Express the heavy-ball (momentum) method as a damped Hamiltonian
system by pairing a potential function with quadratic kinetic energy.

The difficulty is bookkeeping: we must package a convex, differentiable
potential into a `ConvexHamiltonian` and then apply the damped drift.

Solution Structure.
1. Build a Hamiltonian with quadratic kinetic energy and user-supplied V.
2. Define the heavy-ball drift as the damped Hamiltonian drift.
-/

namespace Gibbs.Hamiltonian.Examples

noncomputable section

/-! ## Momentum Hamiltonian -/

/-- Gradient flow for an objective: q̇ = -∇V(q). -/
noncomputable def gradientFlow (n : ℕ) (V : Config n → ℝ) : Config n → Config n := by
  -- Use the negative gradient direction.
  exact fun q => -gradient V q

/-- Hamiltonian for a convex objective with quadratic kinetic energy. -/
noncomputable def momentumHamiltonian (n : ℕ) (V : Config n → ℝ)
    (hVconv : ConvexOn ℝ Set.univ V) (hVdiff : Differentiable ℝ V) :
    ConvexHamiltonian n := by
  -- Combine quadratic kinetic energy with the given potential.
  exact
    { T := quadraticKinetic n
      V := V
      T_convex := quadraticKinetic_convex n
      V_convex := hVconv
      T_diff := quadraticKinetic_diff n
      V_diff := hVdiff }

/-! ## Heavy-Ball Drift -/

/-- Heavy-ball (momentum) method as a damped Hamiltonian drift. -/
noncomputable def heavyBallDrift (n : ℕ) (V : Config n → ℝ)
    (hVconv : ConvexOn ℝ Set.univ V) (hVdiff : Differentiable ℝ V)
    (d : Damping) : PhasePoint n → PhasePoint n := by
  -- Apply the damped drift to the momentum Hamiltonian.
  exact dampedDrift (momentumHamiltonian n V hVconv hVdiff) d

/-! ## Comparison with Gradient Flow -/

/-- If momentum equals the negative gradient, the q-dynamics match gradient flow. -/
theorem heavyBall_q_equals_gradientFlow (n : ℕ) (V : Config n → ℝ)
    (hVconv : ConvexOn ℝ Set.univ V) (hVdiff : Differentiable ℝ V)
    (d : Damping) (x : PhasePoint n)
    (hp : x.p = -gradient V x.q) :
    (heavyBallDrift n V hVconv hVdiff d x).q = gradientFlow n V x.q := by
  -- Expand the q-component and use ∇(½‖·‖²) = id.
  simp [heavyBallDrift, dampedDrift_q, momentumHamiltonian, gradientFlow,
    ConvexHamiltonian.velocity, quadraticKinetic_grad, hp]

end

end Gibbs.Hamiltonian.Examples
